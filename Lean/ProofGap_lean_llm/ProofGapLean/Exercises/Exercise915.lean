import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise915

noncomputable section

def y (a x : ℝ) : ℝ :=
  Real.arctan (x ^ 2 / a)

def expandedDerivative (a x : ℝ) : ℝ :=
  1 / (1 + (x ^ 2 / a) ^ 2) * (2 * x / a)

def finalDerivative (a x : ℝ) : ℝ :=
  2 * a * x / (a ^ 2 + x ^ 4)

/-- Exercise 915, gap 1; the scale in the arctangent
argument must be nonzero. -/
theorem gap1 (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (y a) (expandedDerivative a x) x := by
  have hinner :
      HasDerivAt (fun z : ℝ => z ^ 2 / a) (2 * x / a) x := by
    simpa [pow_two, two_mul] using
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const a)
  simpa [y, expandedDerivative, Function.comp_def] using
    (Real.hasDerivAt_arctan (x ^ 2 / a)).comp x hinner

/-- Exercise 915, gap 2; a nonzero scale validates all
displayed divisions. -/
theorem gap2 (a x : ℝ) (ha : a ≠ 0) :
    expandedDerivative a x = finalDerivative a x := by
  have harg : 1 + (x ^ 2 / a) ^ 2 ≠ 0 := by
    positivity
  have hfinal : a ^ 2 + x ^ 4 ≠ 0 := by
    exact ne_of_gt
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (by positivity))
  unfold expandedDerivative finalDerivative
  field_simp [ha, harg, hfinal]

/-- Exercise 915, gap 3; retain the nonzero scale in the
final derivative formula. -/
theorem gap3 (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (y a) (finalDerivative a x) x := by
  rw [← gap2 a x ha]
  exact gap1 a x ha

end

end ProofGap.Exercise915
