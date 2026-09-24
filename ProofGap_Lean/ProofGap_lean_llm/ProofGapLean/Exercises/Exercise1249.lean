import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.Tendsto

namespace ProofGap.Exercise1249

noncomputable section

open Filter

def f (x : ℝ) : ℝ :=
  if 0 < x then x * Real.sin (Real.log x) else 0

def MeanValueSelector (ξ : ℝ → ℝ) : Prop :=
  ∀ x > 0, 0 < ξ x ∧ ξ x < x ∧
    f x - f 0 = x * deriv f (ξ x)

private theorem sin_phase_nat_eq_one (N : ℕ) :
    Real.sin (Real.pi / 2 - 2 * (N : ℝ) * Real.pi) = 1 := by
  induction N with
  | zero => norm_num [Real.sin_pi_div_two]
  | succ N ih =>
      calc
        Real.sin (Real.pi / 2 - 2 * ((N + 1 : ℕ) : ℝ) * Real.pi) =
            Real.sin ((Real.pi / 2 - 2 * (N : ℝ) * Real.pi) -
              2 * Real.pi) := by
          congr 1
          rw [Nat.cast_add, Nat.cast_one]
          ring
        _ = Real.sin (Real.pi / 2 - 2 * (N : ℝ) * Real.pi) := by
          rw [Real.sin_sub_two_pi]
        _ = 1 := ih

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv f x = Real.sin (Real.log x) + Real.cos (Real.log x) := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (Real.log y))
        (Real.cos (Real.log x) * x⁻¹) x :=
    (Real.hasDerivAt_sin (Real.log x)).comp x hlog
  have hp :
      HasDerivAt (fun y : ℝ => y * Real.sin (Real.log y))
        (1 * Real.sin (Real.log x) +
          x * (Real.cos (Real.log x) * x⁻¹)) x :=
    (hasDerivAt_id x).mul hsin
  have hp' :
      HasDerivAt (fun y : ℝ => y * Real.sin (Real.log y))
        (Real.sin (Real.log x) + Real.cos (Real.log x)) x := by
    convert hp using 1
    field_simp [hx.ne']
  have heq :
      f =ᶠ[nhds x] (fun y : ℝ => y * Real.sin (Real.log y)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    change 0 < y at hy
    rw [f, if_pos hy]
  exact (hp'.congr_of_eventuallyEq heq).deriv

theorem gap2 (x : ℝ) (hx : 0 < x) :
    Real.sin (Real.log x) + Real.cos (Real.log x) =
      Real.sqrt 2 * Real.sin (Real.pi / 4 + Real.log x) := by
  rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  calc
    Real.sin (Real.log x) + Real.cos (Real.log x) =
        (2 / 2) * (Real.sin (Real.log x) + Real.cos (Real.log x)) := by
      ring
    _ = ((Real.sqrt 2) ^ 2 / 2) *
        (Real.sin (Real.log x) + Real.cos (Real.log x)) := by
      rw [hs]
    _ = Real.sqrt 2 *
        (Real.sqrt 2 / 2 * Real.cos (Real.log x) +
          Real.sqrt 2 / 2 * Real.sin (Real.log x)) := by
      ring

theorem gap3 (x : ℝ) (hx : 0 < x) :
    deriv f x =
      Real.sqrt 2 * Real.sin (Real.pi / 4 + Real.log x) := by
  rw [gap1 x hx, gap2 x hx]

theorem gap4 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ) (x : ℝ) (hx : 0 < x) :
    x * Real.sin (Real.log x) =
      x * Real.sqrt 2 * Real.sin (Real.pi / 4 + Real.log (ξ x)) := by
  rcases hξ x hx with ⟨hξpos, hξlt, hmv⟩
  rw [gap3 (ξ x) hξpos] at hmv
  have hzero : ¬(0 : ℝ) < 0 := lt_irrefl 0
  simpa only [f, if_pos hx, if_neg hzero, sub_zero, mul_assoc] using hmv

theorem gap5 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ) (x : ℝ) (hx : 0 < x) :
    Real.sin (Real.log x) =
      Real.sqrt 2 * Real.sin (Real.pi / 4 + Real.log (ξ x)) := by
  have h := gap4 ξ hξ x hx
  nlinarith

theorem gap6 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N := by
  exact ⟨1, by norm_num⟩

theorem gap7 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧
      -2 * (N : ℝ) * Real.pi + Real.pi / 4 < Real.log (ξ (ε / 2)) := by
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (|Real.log (ξ (ε / 2))| + 1)
  let N : ℕ := n + 1
  have hN :
      |Real.log (ξ (ε / 2))| + 1 < (N : ℝ) := by
    dsimp [N]
    exact lt_trans hn (by norm_num)
  have hcoef : 0 < 2 * (N : ℝ) - 1 / 4 := by
    nlinarith [abs_nonneg (Real.log (ξ (ε / 2)))]
  have hp : 0 < (Real.pi - 3) * (2 * (N : ℝ) - 1 / 4) :=
    mul_pos (by nlinarith [Real.pi_gt_three]) hcoef
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    omega
  · nlinarith [neg_le_abs (Real.log (ξ (ε / 2)))]

theorem gap8 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ) :
    Tendsto ξ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact lt_trans ha (hξ x hx).1
  · intro b hb
    have hxb : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), x < b :=
      (tendsto_id.mono_left inf_le_left).eventually (Iio_mem_nhds hb)
    filter_upwards [hxb, self_mem_nhdsWithin] with x hxlt hx
    exact lt_trans (hξ x hx).2.1 hxlt

theorem gap9 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ) :
    Tendsto (fun x => Real.log (ξ x)) (nhdsWithin 0 (Set.Ioi 0)) atBot := by
  refine tendsto_atBot.2 ?_
  intro b
  have hevent :
      ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), ξ x < Real.exp b :=
    (gap8 ξ hξ).eventually (Iio_mem_nhds (Real.exp_pos b))
  filter_upwards [hevent, self_mem_nhdsWithin] with x hxexp hx
  have hpos : 0 < ξ x := (hξ x hx).1
  have hexp : Real.exp (Real.log (ξ x)) < Real.exp b := by
    simpa [Real.exp_log hpos] using hxexp
  exact le_of_lt ((Real.exp_lt_exp).mp hexp)

theorem gap10 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ, 0 < δ := by
  exact ⟨1, by norm_num⟩

theorem gap11 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ < ε / 2 := by
  refine ⟨ε / 4, ?_, ?_⟩ <;> nlinarith

theorem gap12 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) (ε / 2),
      Real.log (ξ δ) < -2 * (N : ℝ) * Real.pi + Real.pi / 4 := by
  let A : ℝ := -2 * (N : ℝ) * Real.pi + Real.pi / 4
  have hlog :
      ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), Real.log (ξ δ) < A :=
    (gap9 ξ hξ).eventually (eventually_lt_atBot A)
  have hupper :
      ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), δ < ε / 2 :=
    (tendsto_id.mono_left inf_le_left).eventually
      (Iio_mem_nhds (by nlinarith))
  have hall :
      ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
        δ ∈ Set.Ioo (0 : ℝ) (ε / 2) ∧ Real.log (ξ δ) < A := by
    filter_upwards [hlog, hupper, self_mem_nhdsWithin] with δ hdlog hdu hdp
    exact ⟨⟨hdp, hdu⟩, hdlog⟩
  rcases hall.exists with ⟨δ, hδ, hdlog⟩
  exact ⟨δ, hδ, by simpa [A] using hdlog⟩

theorem gap13 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hcont : ContinuousOn ξ (Set.Ioo 0 ε)) :
    ∃ x₀ ∈ Set.Ioo (0 : ℝ) (ε / 2),
      Real.log (ξ x₀) = -2 * (N : ℝ) * Real.pi + Real.pi / 4 := by
  rcases gap7 ξ hξ ε hε with ⟨M, hM, hhigh⟩
  rcases gap12 ξ hξ ε hε M with ⟨δ, hδ, hlow⟩
  let g : ℝ → ℝ := fun x => Real.log (ξ x)
  let A : ℝ := -2 * (M : ℝ) * Real.pi + Real.pi / 4
  have hgcont : ContinuousOn g (Set.Ioo 0 ε) := by
    intro x hx
    have hpos : 0 < ξ x := (hξ x hx.1).1
    exact (Real.continuousAt_log hpos.ne').comp_continuousWithinAt
      (hcont x hx)
  have hsubset : Set.Icc δ (ε / 2) ⊆ Set.Ioo (0 : ℝ) ε := by
    intro y hy
    constructor
    · exact lt_of_lt_of_le hδ.1 hy.1
    · exact lt_of_le_of_lt hy.2 (by nlinarith)
  have hgIcc : ContinuousOn g (Set.Icc δ (ε / 2)) :=
    hgcont.mono hsubset
  have hbetween : A ∈ Set.Icc (g δ) (g (ε / 2)) := by
    constructor
    · exact le_of_lt (by simpa [g, A] using hlow)
    · exact le_of_lt (by simpa [g, A] using hhigh)
  have himage :=
    intermediate_value_Icc (le_of_lt hδ.2) hgIcc hbetween
  rcases himage with ⟨y, hy, hphase⟩
  have hypos : 0 < y := lt_of_lt_of_le hδ.1 hy.1
  have hphase' :
      Real.log (ξ y) = -2 * (M : ℝ) * Real.pi + Real.pi / 4 := by
    simpa [g, A] using hphase
  have hsine :
      Real.sin (Real.pi / 4 + Real.log (ξ y)) = 1 := by
    rw [hphase']
    have hang :
        Real.pi / 4 + (-2 * (M : ℝ) * Real.pi + Real.pi / 4) =
          Real.pi / 2 - 2 * (M : ℝ) * Real.pi := by
      ring
    rw [hang, sin_phase_nat_eq_one]
  have heq : Real.sin (Real.log y) = Real.sqrt 2 := by
    calc
      Real.sin (Real.log y) =
          Real.sqrt 2 * Real.sin (Real.pi / 4 + Real.log (ξ y)) :=
        gap5 ξ hξ y hypos
      _ = Real.sqrt 2 := by rw [hsine, mul_one]
  have hsin := Real.sin_le_one (Real.log y)
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hfalse : False := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  exact hfalse.elim

theorem gap14 (x₀ : ℝ) :
    Real.sin (Real.log x₀) ≤ 1 := by
  exact Real.sin_le_one (Real.log x₀)

theorem gap15 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ) (x₀ : ℝ) (hx₀ : 0 < x₀) :
    Real.sin (Real.log x₀) =
      Real.sqrt 2 * Real.sin (Real.pi / 4 + Real.log (ξ x₀)) := by
  exact gap5 ξ hξ x₀ hx₀

theorem gap16 (ξ : ℝ → ℝ) (x₀ : ℝ) (N : ℕ)
    (hphase : Real.log (ξ x₀) =
      -2 * (N : ℝ) * Real.pi + Real.pi / 4) :
    Real.sqrt 2 * Real.sin (Real.pi / 4 + Real.log (ξ x₀)) =
      Real.sqrt 2 := by
  rw [hphase]
  have hang :
      Real.pi / 4 + (-2 * (N : ℝ) * Real.pi + Real.pi / 4) =
        Real.pi / 2 - 2 * (N : ℝ) * Real.pi := by
    ring
  rw [hang, sin_phase_nat_eq_one, mul_one]

theorem gap17 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ)
    (ε : ℝ) (hε : 0 < ε) (hcont : ContinuousOn ξ (Set.Ioo 0 ε)) :
    (1 : ℝ) ≥ Real.sqrt 2 := by
  rcases gap13 ξ hξ ε hε 0 hcont with ⟨x₀, hx₀, hphase⟩
  have heq : Real.sin (Real.log x₀) = Real.sqrt 2 :=
    (gap15 ξ hξ x₀ hx₀.1).trans (gap16 ξ x₀ 0 hphase)
  nlinarith [gap14 x₀]

theorem gap18 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ)
    (ε : ℝ) (hε : 0 < ε) (hcont : ContinuousOn ξ (Set.Ioo 0 ε)) :
    False := by
  have hle := gap17 ξ hξ ε hε hcont
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem gap19 (ξ : ℝ → ℝ) (hξ : MeanValueSelector ξ) (ε : ℝ) (hε : 0 < ε) :
    ¬ContinuousOn ξ (Set.Ioo 0 ε) := by
  intro hcont
  exact gap18 ξ hξ ε hε hcont

end

end ProofGap.Exercise1249
