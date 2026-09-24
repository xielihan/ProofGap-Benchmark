import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1671

noncomputable section

def integrand (x : ℝ) : ℝ := Real.sinh (2 * x + 1) + Real.cosh (2 * x - 1)
def primitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.cosh (2 * x + 1) + Real.sinh (2 * x - 1))

theorem gap1 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hplus : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    convert ((hasDerivAt_id x).const_mul 2).add_const 1 using 1 <;> ring
  have hminus : HasDerivAt (fun y : ℝ => 2 * y - 1) 2 x := by
    convert ((hasDerivAt_id x).const_mul 2).sub_const 1 using 1 <;> ring
  have hc :
      HasDerivAt (fun y : ℝ => Real.cosh (2 * y + 1))
        (Real.sinh (2 * x + 1) * 2) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cosh (2 * x + 1)).comp x hplus
  have hs :
      HasDerivAt (fun y : ℝ => Real.sinh (2 * y - 1))
        (Real.cosh (2 * x - 1) * 2) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sinh (2 * x - 1)).comp x hminus
  unfold primitive integrand
  convert (hc.add hs).const_mul (1 / 2 : ℝ) using 1 <;> ring

end

end ProofGap.Exercise1671
