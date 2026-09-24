import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1653

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x
def primitive (x : ℝ) : ℝ := x - coth x
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem hasDerivAt_primitive {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (1 + 1 / Real.sinh x ^ 2) x := by
  change 0 < x at hx
  have hsinh_pos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hsinh : Real.sinh x ≠ 0 := ne_of_gt hsinh_pos
  have hquot :
      HasDerivAt coth
        ((Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) /
          Real.sinh x ^ 2) x := by
    simpa [coth] using
      (Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hsinh
  have hbase :
      HasDerivAt primitive
        (1 - (Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) /
          Real.sinh x ^ 2) x := by
    simpa [primitive] using (hasDerivAt_id x).sub hquot
  have hcoef :
      1 - (Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) /
          Real.sinh x ^ 2 =
        1 + 1 / Real.sinh x ^ 2 := by
    field_simp [hsinh]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [hcoef] at hbase
  exact hbase

private theorem value_eq_at_one_of_hasDerivAt_zero
    (H : ℝ → ℝ)
    (hH : ∀ x ∈ domain, HasDerivAt H 0 x)
    (x : ℝ) (hx : x ∈ domain) :
    H x = H 1 := by
  change 0 < x at hx
  by_cases hxeq : x = 1
  · simpa [hxeq]
  · rcases lt_or_gt_of_ne hxeq with hxl | hxl
    · have hcont : ContinuousOn H (Set.Icc x 1) := by
        intro y hy
        exact
          (hH y (by
            change 0 < y
            exact hx.trans_le hy.1)).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ H (Set.Ioo x 1) := by
        intro y hy
        exact
          (hH y (by
            change 0 < y
            exact hx.trans hy.1)).differentiableAt.differentiableWithinAt
      obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope H hxl hcont hdiff
      have hz : deriv H c = 0 :=
        (hH c (by
          change 0 < c
          exact hx.trans hc.1)).deriv
      rw [hz] at hslope
      have hden : (1 : ℝ) - x ≠ 0 := ne_of_gt (sub_pos.mpr hxl)
      field_simp [hden] at hslope
      linarith
    · have hcont : ContinuousOn H (Set.Icc 1 x) := by
        intro y hy
        exact
          (hH y (by
            change 0 < y
            exact zero_lt_one.trans_le hy.1)).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ H (Set.Ioo 1 x) := by
        intro y hy
        exact
          (hH y (by
            change 0 < y
            exact zero_lt_one.trans hy.1)).differentiableAt.differentiableWithinAt
      obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope H hxl hcont hdiff
      have hz : deriv H c = 0 :=
        (hH c (by
          change 0 < c
          exact zero_lt_one.trans hc.1)).deriv
      rw [hz] at hslope
      have hden : x - (1 : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hxl)
      field_simp [hden] at hslope
      linarith

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    coth x ^ 2 = 1 + 1 / Real.sinh x ^ 2 := by
  change 0 < x at hx
  have hsinh_pos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hsinh : Real.sinh x ≠ 0 := ne_of_gt hsinh_pos
  unfold coth
  field_simp [hsinh]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem gap2 :
    AntiderivativesOn (fun x => coth x ^ 2) =
      AntiderivativesOn (fun x => 1 + 1 / Real.sinh x ^ 2) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact (hderiv x hx).trans (gap1 x hx)
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact (hderiv x hx).trans (gap1 x hx).symm

theorem gap3 :
    AntiderivativesOn (fun x => 1 + 1 / Real.sinh x ^ 2) =
      PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  have hopen : IsOpen domain := by
    exact isOpen_Ioi
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hzero :
        ∀ x ∈ domain, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      have hFat :=
        ((hFdiff x hx).differentiableAt (hopen.mem_nhds hx)).hasDerivAt
      rw [hFderiv x hx] at hFat
      simpa using hFat.sub (hasDerivAt_primitive hx)
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hconst := value_eq_at_one_of_hasDerivAt_zero
      (fun y => F y - primitive y) hzero x hx
    dsimp at hconst
    linarith
  · rintro ⟨C, hFC⟩
    have hFat :
        ∀ x ∈ domain, HasDerivAt F
          (1 + 1 / Real.sinh x ^ 2) x := by
      intro x hx
      exact ((hasDerivAt_primitive hx).add_const C).congr_of_eventuallyEq (by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hFC y hy)
    constructor
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

theorem gap4 :
    AntiderivativesOn (fun x => coth x ^ 2) =
      PrimitiveFamily primitive := by
  exact gap2.trans gap3

end
end ProofGap.Exercise1653
