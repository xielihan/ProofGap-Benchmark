import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1666

noncomputable section

def integrand (α x : ℝ) : ℝ := Real.sin (5 * x) - Real.sin (5 * α)
def primitive (α x : ℝ) : ℝ :=
  -(1 / 5 : ℝ) * Real.cos (5 * x) - x * Real.sin (5 * α)

theorem gap1 (α x : ℝ) :
    HasDerivAt (primitive α) (integrand α x) x := by
  unfold primitive integrand
  convert
    (((Real.hasDerivAt_cos (5 * x)).comp x
        ((hasDerivAt_id x).const_mul 5)).const_mul (-(1 / 5 : ℝ))).sub
      ((hasDerivAt_id x).mul_const (Real.sin (5 * α))) using 1 <;>
    ring

end

end ProofGap.Exercise1666
