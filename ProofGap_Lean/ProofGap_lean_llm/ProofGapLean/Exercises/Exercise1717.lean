import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1717

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) :=
  Real.cos x / Real.sqrt (2 + Real.cos (2 * x))
def substitutedIntegrand (x : ℝ) :=
  deriv Real.sin x / Real.sqrt (3 - 2 * (Real.sin x) ^ 2)
def primitive (x : ℝ) :=
  1 / Real.sqrt 2 *
    Real.arcsin (Real.sqrt (2 / 3 : ℝ) * Real.sin x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  let t : ℝ := Real.sqrt (2 / 3 : ℝ)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = (2 / 3 : ℝ) := by
    dsimp [t]
    exact Real.sq_sqrt (by norm_num)
  have ht1 : t < 1 := by
    nlinarith
  have hslo : -1 ≤ Real.sin x := Real.neg_one_le_sin x
  have hshi : Real.sin x ≤ 1 := Real.sin_le_one x
  have hzlo : -1 < t * Real.sin x := by
    have hmul := mul_le_mul_of_nonneg_left hslo ht0
    nlinarith
  have hzhi : t * Real.sin x < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hshi ht0
    nlinarith
  have hin : HasDerivAt (fun y => t * Real.sin y) (t * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul t
  have harc0 : HasDerivAt Real.arcsin
      (1 / Real.sqrt (1 - (t * Real.sin x) ^ 2)) (t * Real.sin x) :=
    Real.hasDerivAt_arcsin (x := t * Real.sin x)
      (ne_of_gt hzlo) (ne_of_lt hzhi)
  have harc : HasDerivAt (fun y => Real.arcsin (t * Real.sin y))
      ((1 / Real.sqrt (1 - (t * Real.sin x) ^ 2)) * (t * Real.cos x)) x := by
    simpa only [Function.comp_apply] using harc0.comp x hin
  have hplus : 0 ≤ 1 + Real.sin x := by
    linarith
  have hsinprod : 0 ≤ (1 - Real.sin x) * (1 + Real.sin x) :=
    mul_nonneg (sub_nonneg.mpr hshi) hplus
  have hs2 : (Real.sin x) ^ 2 ≤ 1 := by
    nlinarith
  have hA : 0 < 3 - 2 * (Real.sin x) ^ 2 := by
    nlinarith
  have hden : 1 - (t * Real.sin x) ^ 2 =
      (3 - 2 * (Real.sin x) ^ 2) / 3 := by
    nlinarith
  have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsqrt3 : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hsqrtA : Real.sqrt (3 - 2 * (Real.sin x) ^ 2) ≠ 0 := by
    positivity
  have htform : t = Real.sqrt 2 / Real.sqrt 3 := by
    dsimp [t]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  have hdform : Real.sqrt (1 - (t * Real.sin x) ^ 2) =
      Real.sqrt (3 - 2 * (Real.sin x) ^ 2) / Real.sqrt 3 := by
    rw [hden, Real.sqrt_div (le_of_lt hA)]
  have hcoef :
      (1 / Real.sqrt 2) *
          ((1 / Real.sqrt (1 - (t * Real.sin x) ^ 2)) *
            (t * Real.cos x)) =
        Real.cos x / Real.sqrt (3 - 2 * (Real.sin x) ^ 2) := by
    rw [hdform, htform]
    field_simp [hsqrt2, hsqrt3, hsqrtA]
    <;> ring
  have hscaled := harc.const_mul (1 / Real.sqrt 2)
  rw [hcoef] at hscaled
  unfold primitive substitutedIntegrand
  rw [Real.deriv_sin]
  simpa [t] using hscaled

private theorem derivZero_eq_at_zero (q : ℝ → ℝ)
    (hq : ∀ x : ℝ, HasDerivAt q 0 x) :
    ∀ x : ℝ, q x = q 0 := by
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hcont : ContinuousOn q (Set.Icc x 0) := by
      intro y hy
      exact (hq y).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ q (Set.Ioo x 0) := by
      intro y hy
      exact (hq y).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope⟩ :=
      exists_deriv_eq_slope (f := q) hx hcont hdiff
    have hd : deriv q c = 0 := (hq c).deriv
    have hs0 : (q 0 - q x) / (0 - x) = 0 := by
      linarith
    have hne : 0 - x ≠ 0 := by
      linarith
    field_simp [hne] at hs0
    linarith
  · simpa [hx]
  · have hcont : ContinuousOn q (Set.Icc 0 x) := by
      intro y hy
      exact (hq y).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ q (Set.Ioo 0 x) := by
      intro y hy
      exact (hq y).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope⟩ :=
      exists_deriv_eq_slope (f := q) hx hcont hdiff
    have hd : deriv q c = 0 := (hq c).deriv
    have hs0 : (q x - q 0) / (x - 0) = 0 := by
      linarith
    have hne : x - 0 ≠ 0 := by
      linarith
    field_simp [hne] at hs0
    linarith

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn substitutedIntegrand := by
  have hfun : ∀ x : ℝ, integrand x = substitutedIntegrand x := by
    intro x
    unfold integrand substitutedIntegrand
    rw [Real.deriv_sin]
    have htrig : 2 + Real.cos (2 * x) = 3 - 2 * (Real.sin x) ^ 2 := by
      rw [show 2 * x = x + x by ring, Real.cos_add]
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [htrig]
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    rw [← hfun x]
    exact h x hx
  · intro h x hx
    rw [hfun x]
    exact h x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hzero : ∀ y : ℝ,
        HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y
      convert (hF y (Set.mem_univ y)).sub (primitive_hasDerivAt y) using 1 <;> ring
    have hc := derivZero_eq_at_zero (fun z => F z - primitive z) hzero x
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hC y (Set.mem_univ y)
    rw [hEq]
    simpa [add_comm] using (primitive_hasDerivAt x).const_add C
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1717
