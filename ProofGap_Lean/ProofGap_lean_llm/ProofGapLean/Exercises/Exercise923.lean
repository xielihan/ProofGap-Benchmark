import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise923

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arcsin (Real.sin x - Real.cos x)

def expandedDerivative (x : ℝ) : ℝ :=
  (Real.cos x + Real.sin x) /
    Real.sqrt (1 - (Real.sin x - Real.cos x) ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  (Real.sin x + Real.cos x) / Real.sqrt (Real.sin (2 * x))

/-- Exercise 923, gap 1; positivity of `sin (2x)` is
equivalent to the inverse-sine argument lying strictly inside `(-1,1)`. -/
private theorem sin_sub_cos_sq_identity (x : ℝ) :
    1 - (Real.sin x - Real.cos x) ^ 2 = Real.sin (2 * x) := by
  rw [Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap1 (x : ℝ) (hx : 0 < Real.sin (2 * x)) :
    HasDerivAt y (expandedDerivative x) x := by
  have hsquare : (Real.sin x - Real.cos x) ^ 2 < 1 := by
    nlinarith [hx, sin_sub_cos_sq_identity x]
  have harg : Real.sin x - Real.cos x ∈ Set.Ioo (-1) 1 := by
    constructor
    · nlinarith [
        hsquare,
        sq_nonneg ((Real.sin x - Real.cos x) + 1)
      ]
    · nlinarith [
        hsquare,
        sq_nonneg ((Real.sin x - Real.cos x) - 1)
      ]
  have hne_neg : Real.sin x - Real.cos x ≠ -1 := ne_of_gt harg.1
  have hne_pos : Real.sin x - Real.cos x ≠ 1 := ne_of_lt harg.2
  have hsin : HasDerivAt Real.sin (Real.cos x) x := by
    simpa using (hasDerivAt_id x).sin
  have hcos : HasDerivAt Real.cos (-Real.sin x) x := by
    simpa using (hasDerivAt_id x).cos
  have hinner :
      HasDerivAt (fun t : ℝ => Real.sin t - Real.cos t)
        (Real.cos x + Real.sin x) x := by
    simpa only [sub_neg_eq_add] using hsin.sub hcos
  have harcsin :
      HasDerivAt Real.arcsin
        (1 / Real.sqrt (1 - (Real.sin x - Real.cos x) ^ 2))
        (Real.sin x - Real.cos x) := by
    apply Real.hasDerivAt_arcsin <;> assumption
  simpa [y, expandedDerivative, div_eq_mul_inv, mul_comm] using
    harcsin.comp x hinner

/-- Exercise 923, gap 2; the positive radicand permits the
displayed square-root rewrite. -/
theorem gap2 (x : ℝ) (hx : 0 < Real.sin (2 * x)) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  rw [sin_sub_cos_sq_identity x]
  rw [add_comm (Real.cos x) (Real.sin x)]

/-- Exercise 923, gap 3; retain the real differentiability
domain of the inverse-sine composition. -/
theorem gap3 (x : ℝ) (hx : 0 < Real.sin (2 * x)) :
    HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2 x hx] using gap1 x hx

end

end ProofGap.Exercise923
