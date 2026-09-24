import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3204

noncomputable section

open Filter
open scoped Topology

def f (x y : ℝ) : ℝ :=
  if y = 0 then 0 else x * Real.sin (1 / y)

def jointFunction (p : ℝ × ℝ) : ℝ :=
  f p.1 p.2

def SingularPoint (g : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : Prop :=
  ¬ ContinuousAt g p

def puncturedZero : Filter ℝ :=
  nhdsWithin (0 : ℝ) (({(0 : ℝ)} : Set ℝ)ᶜ)

theorem gap1 :
    ∀ y₀ x₀ : ℝ, y₀ ≠ 0 →
      ContinuousAt jointFunction (x₀, y₀) := by
  intro y₀ x₀ hy₀
  have hmain :
      ContinuousAt
        (fun p : ℝ × ℝ => p.1 * Real.sin (1 / p.2))
        (x₀, y₀) :=
    continuousAt_fst.mul
      (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.div continuousAt_snd hy₀))
  have hy : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, y₀), p.2 ≠ 0 := by
    exact continuousAt_snd.eventually (eventually_ne_nhds hy₀)
  have heq :
      (fun p : ℝ × ℝ => p.1 * Real.sin (1 / p.2)) =ᶠ[𝓝 (x₀, y₀)]
        jointFunction := by
    filter_upwards [hy] with p hp
    simp [jointFunction, f, hp]
  change
    Tendsto jointFunction (𝓝 (x₀, y₀))
      (𝓝 (jointFunction (x₀, y₀)))
  rw [show jointFunction (x₀, y₀) = x₀ * Real.sin (1 / y₀) by
    simp [jointFunction, f, hy₀]]
  exact hmain.congr' heq

theorem gap2 :
    ContinuousOn jointFunction {p : ℝ × ℝ | p.2 ≠ 0} := by
  intro p hp
  exact (gap1 p.2 p.1 hp).continuousWithinAt

theorem gap3 :
    ∀ x y : ℝ,
      |f x y - f 0 0| = |f x y| := by
  intro x y
  simp [f]

theorem gap4 :
    ∀ x y : ℝ, |f x y| ≤ |x| := by
  intro x y
  unfold f
  split_ifs with hy
  · simp
  · rw [abs_mul]
    calc
      |x| * |Real.sin (1 / y)| ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / y)) (abs_nonneg x)
      _ = |x| := by ring

theorem gap5 :
    ∀ x y : ℝ,
      |f x y - f 0 0| ≤ |x| := by
  intro x y
  calc
    |f x y - f 0 0| = |f x y| := gap3 x y
    _ ≤ |x| := gap4 x y

theorem gap6 :
    ContinuousAt jointFunction ((0, 0) : ℝ × ℝ) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hfst :
      Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 ((0, 0) : ℝ × ℝ)) (𝓝 0) :=
    continuousAt_fst
  have hev := (Metric.tendsto_nhds.1 hfst) ε hε
  filter_upwards [hev] with p hp
  have hp' : |p.1| < ε := by
    simpa [Real.dist_eq] using hp
  change |f p.1 p.2 - f 0 0| < ε
  exact lt_of_le_of_lt (gap5 p.1 p.2) hp'

theorem gap7 :
    ∀ x₀ : ℝ, x₀ ≠ 0 →
      ¬ ∃ L : ℝ,
        Tendsto (fun y : ℝ => f x₀ y) puncturedZero (𝓝 L) := by
  intro x₀ hx₀
  rintro ⟨L, hL⟩
  have hinv :
      Tendsto (fun t : ℝ => 1 / t) atTop puncturedZero := by
    rw [puncturedZero, tendsto_nhdsWithin_iff]
    constructor
    · simpa [one_div] using
        (tendsto_inv_atTop_zero :
          Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      simp [ht0]
  have hraw :
      Tendsto (fun t : ℝ => f x₀ (1 / t)) atTop (𝓝 L) :=
    hL.comp hinv
  have heq :
      (fun t : ℝ => f x₀ (1 / t)) =ᶠ[atTop]
        (fun t : ℝ => x₀ * Real.sin t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp [f, one_div, ht0]
  have hxs :
      Tendsto (fun t : ℝ => x₀ * Real.sin t) atTop (𝓝 L) :=
    hraw.congr' heq
  let M : ℝ := x₀⁻¹ * L
  have hc :
      Tendsto (fun _ : ℝ => x₀⁻¹) atTop (𝓝 x₀⁻¹) :=
    tendsto_const_nhds
  have hsin : Tendsto Real.sin atTop (𝓝 M) := by
    simpa [M, mul_assoc, hx₀] using hc.mul hxs
  have hshift (c : ℝ) :
      Tendsto (fun t : ℝ => t + c) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (b - c)] with t ht
    linarith
  have hpi :
      Tendsto (fun t : ℝ => -Real.sin t) atTop (𝓝 M) := by
    simpa [Function.comp_def, Real.sin_add] using
      hsin.comp (hshift Real.pi)
  have hM : M = -M := tendsto_nhds_unique hpi hsin.neg
  have hM0 : M = 0 := by linarith
  have hsin0 : Tendsto Real.sin atTop (𝓝 0) := by
    simpa [hM0] using hsin
  have hcos0 : Tendsto Real.cos atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sin_add] using
      hsin0.comp (hshift (Real.pi / 2))
  have hsum :
      Tendsto
        (fun t : ℝ =>
          Real.sin t * Real.sin t + Real.cos t * Real.cos t)
        atTop (𝓝 0) := by
    simpa using (hsin0.mul hsin0).add (hcos0.mul hcos0)
  have hfun :
      (fun t : ℝ =>
        Real.sin t * Real.sin t + Real.cos t * Real.cos t) =
        (fun _ : ℝ => 1) := by
    funext t
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hfun] at hsum
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hzeroone : (0 : ℝ) = 1 := tendsto_nhds_unique hsum hone
  linarith

theorem gap8 :
    ∀ x₀ : ℝ, x₀ ≠ 0 →
      SingularPoint jointFunction (x₀, 0) := by
  intro x₀ hx₀
  unfold SingularPoint
  intro hc
  have hp : ContinuousAt (fun y : ℝ => (x₀, y)) 0 :=
    continuousAt_const.prodMk continuousAt_id
  have hp' :
      Tendsto (fun y : ℝ => (x₀, y)) puncturedZero
        (𝓝 ((x₀, 0) : ℝ × ℝ)) := by
    rw [puncturedZero]
    exact hp.mono_left inf_le_left
  have hcomp :
      Tendsto (fun y : ℝ => jointFunction (x₀, y)) puncturedZero
        (𝓝 (jointFunction (x₀, 0))) :=
    Tendsto.comp hc hp'
  apply (gap7 x₀ hx₀)
  refine ⟨0, ?_⟩
  simpa [jointFunction, f] using hcomp

theorem gap9 :
    {p : ℝ × ℝ | SingularPoint jointFunction p} =
      {p : ℝ × ℝ | p.2 = 0 ∧ p.1 ≠ 0} := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.fst, Prod.snd]
  constructor
  · intro hs
    have hy : y = 0 := by
      by_contra hy
      exact hs (gap1 y x hy)
    have hx : x ≠ 0 := by
      intro hx
      subst x
      subst y
      exact hs gap6
    exact ⟨hy, hx⟩
  · rintro ⟨rfl, hx⟩
    exact gap8 x hx

theorem gap10 :
    ((0, 0) : ℝ × ℝ) ∈
      closure {p : ℝ × ℝ | SingularPoint jointFunction p} := by
  rw [gap9]
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  refine ⟨((ε / 2, 0) : ℝ × ℝ), ?_, ?_⟩
  · change (0 : ℝ) = 0 ∧ ε / 2 ≠ 0
    constructor
    · rfl
    · exact div_ne_zero hε.ne' (by norm_num)
  · have heps2 : 0 ≤ ε / 2 := by linarith
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero, zero_sub, abs_zero, abs_neg,
      max_eq_left (abs_nonneg (ε / 2))]
    rw [abs_of_nonneg heps2]
    linarith

theorem gap11 :
    ((0, 0) : ℝ × ℝ) ∉
      {p : ℝ × ℝ | SingularPoint jointFunction p} := by
  intro h
  exact h gap6

theorem gap12 :
    closure {p : ℝ × ℝ | SingularPoint jointFunction p} ≠
      {p : ℝ × ℝ | SingularPoint jointFunction p} := by
  intro h
  have hmem := gap10
  rw [h] at hmem
  exact gap11 hmem

theorem gap13 :
    closure {p : ℝ × ℝ | SingularPoint jointFunction p} ≠
      {p : ℝ × ℝ | SingularPoint jointFunction p} := by
  exact gap12

end

end ProofGap.Exercise3204
