import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3202

noncomputable section

open Filter
open scoped Topology

def f (x y : ℝ) : ℝ :=
  if x ^ 2 + y ^ 2 = 0 then 0 else 2 * x * y / (x ^ 2 + y ^ 2)

def g (a x : ℝ) : ℝ :=
  f x a

def jointFunction (p : ℝ × ℝ) : ℝ :=
  f p.1 p.2

def lineExpression (k x : ℝ) : ℝ :=
  2 * k * x ^ 2 / (x ^ 2 * (1 + k ^ 2))

def puncturedOrigin : Filter (ℝ × ℝ) :=
  nhdsWithin ((0, 0) : ℝ × ℝ)
    (({((0, 0) : ℝ × ℝ)} : Set (ℝ × ℝ))ᶜ)

def puncturedZero : Filter ℝ :=
  nhdsWithin (0 : ℝ) (({(0 : ℝ)} : Set ℝ)ᶜ)

private theorem f_eq_div (x y : ℝ) :
    f x y = 2 * x * y / (x ^ 2 + y ^ 2) := by
  by_cases h : x ^ 2 + y ^ 2 = 0 <;> simp [f, h]

theorem gap1 :
    ∀ x a : ℝ, a ≠ 0 →
      g a x =
        if x ≠ 0 then 2 * a * x / (x ^ 2 + a ^ 2) else 0 := by
  intro x a ha
  rw [g, f_eq_div]
  by_cases hx : x = 0
  · simp [hx]
  · simp only [if_pos hx]
    ring

theorem gap2 :
    ∀ x a : ℝ, a ≠ 0 →
      g a x = 2 * a * x / (x ^ 2 + a ^ 2) := by
  intro x a ha
  rw [g, f_eq_div]
  ring

theorem gap3 :
    ∀ a : ℝ, a ≠ 0 → Continuous (g a) := by
  intro a ha
  have hg : g a = fun x : ℝ => 2 * a * x / (x ^ 2 + a ^ 2) := by
    funext x
    exact gap2 x a ha
  rw [hg]
  exact (continuous_const.mul continuous_id).div
    ((continuous_id.pow 2).add (continuous_const.pow 2))
    (fun x => by nlinarith [sq_nonneg x, sq_pos_of_ne_zero ha])

theorem gap4 :
    ∀ x : ℝ, f x 0 = 0 := by
  intro x
  simp [f]

theorem gap5 :
    Continuous (fun x : ℝ => f x 0) := by
  simpa only [gap4] using
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

theorem gap6 :
    ∀ a : ℝ, Continuous (fun x : ℝ => f x a) := by
  intro a
  by_cases ha : a = 0
  · subst a
    exact gap5
  · simpa only [g] using gap3 a ha

theorem gap7 :
    ∀ a : ℝ, Continuous (fun y : ℝ => f a y) := by
  intro a
  have hfun : (fun y : ℝ => f a y) = fun y : ℝ => f y a := by
    funext y
    unfold f
    have hd : a ^ 2 + y ^ 2 = y ^ 2 + a ^ 2 := by ring
    rw [hd]
    by_cases h : y ^ 2 + a ^ 2 = 0 <;> simp [h] <;> ring
  rw [hfun]
  exact gap6 a

theorem gap8 :
    ContinuousOn jointFunction
      (({((0, 0) : ℝ × ℝ)} : Set (ℝ × ℝ))ᶜ) := by
  have hj : jointFunction =
      (fun p : ℝ × ℝ =>
        2 * p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) := by
    funext p
    simpa only [jointFunction] using f_eq_div p.1 p.2
  rw [hj]
  refine ((continuous_const.mul continuous_fst).mul continuous_snd).continuousOn.div
    (((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousOn) ?_
  intro p hp
  have hpne : p ≠ ((0, 0) : ℝ × ℝ) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp
  intro hden
  have hp1 : p.1 = 0 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have hp2 : p.2 = 0 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  exact hpne (Prod.ext hp1 hp2)

theorem gap9 :
    ∀ k L : ℝ,
      Tendsto jointFunction puncturedOrigin (𝓝 L) →
        Tendsto (lineExpression k) puncturedZero (𝓝 L) := by
  intro k L h
  let φ : ℝ → ℝ × ℝ := fun x => (x, k * x)
  have hφ : Continuous φ :=
    continuous_id.prodMk (continuous_const.mul continuous_id)
  have hc0 : Tendsto φ (𝓝 (0 : ℝ)) (𝓝 (φ 0)) :=
    (hφ.continuousAt : ContinuousAt φ 0)
  have hc : Tendsto φ (𝓝 (0 : ℝ)) (𝓝 ((0, 0) : ℝ × ℝ)) := by
    simpa [φ] using hc0
  have hnhds : Tendsto φ puncturedZero (𝓝 ((0, 0) : ℝ × ℝ)) := by
    apply hc.mono_left
    unfold puncturedZero
    exact inf_le_left
  have hmem : ∀ᶠ x in puncturedZero,
      x ∈ (({(0 : ℝ)} : Set ℝ)ᶜ) := by
    unfold puncturedZero
    exact self_mem_nhdsWithin
  have hprincipal : Tendsto φ puncturedZero
      (Filter.principal (({((0, 0) : ℝ × ℝ)} : Set (ℝ × ℝ))ᶜ)) := by
    refine tendsto_principal.2 ?_
    filter_upwards [hmem] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    change φ x ≠ ((0, 0) : ℝ × ℝ)
    intro hp
    apply hx0
    simpa [φ] using congrArg Prod.fst hp
  have hmap : Tendsto φ puncturedZero puncturedOrigin := by
    unfold puncturedOrigin
    exact (hnhds.inf hprincipal).mono_left (le_inf le_rfl le_rfl)
  have hline : ∀ x : ℝ, jointFunction (φ x) = lineExpression k x := by
    intro x
    change f x (k * x) = lineExpression k x
    rw [f_eq_div]
    unfold lineExpression
    congr 1 <;> ring
  have heq : jointFunction ∘ φ = lineExpression k := by
    funext x
    exact hline x
  rw [← heq]
  exact h.comp hmap

theorem gap10 :
    ∀ k : ℝ,
      Tendsto (lineExpression k) puncturedZero
        (𝓝 (2 * k / (1 + k ^ 2))) := by
  intro k
  have hk : 1 + k ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg k]
  have heq : lineExpression k =ᶠ[puncturedZero]
      (fun _ : ℝ => 2 * k / (1 + k ^ 2)) := by
    unfold puncturedZero
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    simp only [lineExpression]
    field_simp [hx2, hk]
    <;> ring
  exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem gap11 :
    ∀ L : ℝ,
      Tendsto jointFunction puncturedOrigin (𝓝 L) →
        ∀ k : ℝ, L = 2 * k / (1 + k ^ 2) := by
  intro L h k
  have hle : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ puncturedZero := by
    rw [puncturedZero]
    apply nhdsWithin_mono
    intro x hx
    change 0 < x at hx
    change x ≠ 0
    exact ne_of_gt hx
  have h1 := (gap9 k L h).mono_left hle
  have h2 := (gap10 k).mono_left hle
  exact tendsto_nhds_unique h1 h2

theorem gap12 :
    ¬ ∃ L : ℝ,
      Tendsto jointFunction puncturedOrigin (𝓝 L) := by
  rintro ⟨L, h⟩
  have h0 := gap11 L h 0
  have h1 := gap11 L h 1
  norm_num at h0 h1
  linarith

theorem gap13 :
    ¬ ContinuousAt jointFunction ((0, 0) : ℝ × ℝ) := by
  intro h
  apply gap12
  refine ⟨jointFunction ((0, 0) : ℝ × ℝ), ?_⟩
  apply h.mono_left
  rw [puncturedOrigin]
  exact inf_le_left

theorem gap14 :
    (∀ a : ℝ, Continuous (fun x : ℝ => f x a)) ∧
      (∀ a : ℝ, Continuous (fun y : ℝ => f a y)) ∧
      ¬ ContinuousAt jointFunction ((0, 0) : ℝ × ℝ) := by
  exact ⟨gap6, gap7, gap13⟩

end

end ProofGap.Exercise3202
