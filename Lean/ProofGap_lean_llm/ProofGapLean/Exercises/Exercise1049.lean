import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1049

theorem gap1 (p : ℝ) (y : ℝ → ℝ)
    (hcurve : ∀ x, y x ^ 2 = 2 * p * x)
    (hdiff : Differentiable ℝ y) (x : ℝ) :
    2 * y x * deriv y x = 2 * p := by
  have hyderiv : HasDerivAt y (deriv y x) x := (hdiff x).hasDerivAt
  have hcoef :
      deriv y x * y x + y x * deriv y x = 2 * y x * deriv y x := by
    ring
  have hsquare :
      HasDerivAt (fun t : ℝ => y t ^ 2) (2 * y x * deriv y x) x := by
    simpa only [pow_two, hcoef] using hyderiv.mul hyderiv
  have hfun :
      (fun t : ℝ => y t ^ 2) = (fun t : ℝ => 2 * p * t) :=
    funext fun t => hcurve t
  have hderiv_square := hsquare.deriv
  rw [hfun] at hderiv_square
  have hline :
      HasDerivAt (fun t : ℝ => 2 * p * t) (2 * p) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * p)
  exact hderiv_square.symm.trans hline.deriv

theorem gap2 (p : ℝ) (y : ℝ → ℝ)
    (hcurve : ∀ x, y x ^ 2 = 2 * p * x)
    (hdiff : Differentiable ℝ y) (x : ℝ) (hy : y x ≠ 0) :
    deriv y x = p / y x := by
  have hprod : y x * deriv y x = p := by
    apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by simp)
    simpa [mul_assoc] using gap1 p y hcurve hdiff x
  apply (eq_div_iff hy).2
  simpa [mul_comm] using hprod

end ProofGap.Exercise1049
