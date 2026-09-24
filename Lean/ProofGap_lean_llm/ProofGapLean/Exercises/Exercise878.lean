import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise878

noncomputable section

def y (x : ℝ) : ℝ := Real.exp x * (x ^ 2 - 2 * x + 2)
def expandedDerivative (x : ℝ) : ℝ :=
  Real.exp x * (x ^ 2 - 2 * x + 2) + Real.exp x * (2 * x - 2)
def finalDerivative (x : ℝ) : ℝ := x ^ 2 * Real.exp x

theorem gap1 (x : ℝ) : deriv y x = expandedDerivative x := by
  have hexp : HasDerivAt Real.exp (Real.exp x) x := by
    simpa only [Real.deriv_exp] using
      ((Real.differentiableAt_exp : DifferentiableAt ℝ Real.exp x).hasDerivAt)
  have hpoly :
      HasDerivAt (fun t : ℝ => t ^ 2 - 2 * t + 2) (2 * x - 2) x := by
    convert
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).sub
        ((hasDerivAt_id x).const_mul 2)).add_const 2 using 1
    · funext t
      dsimp
      ring
    · simp only [id_eq]
      ring
  simpa [y, expandedDerivative] using (hexp.mul hpoly).deriv
theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  ring
theorem gap3 (x : ℝ) : deriv y x = finalDerivative x := by
  exact (gap1 x).trans (gap2 x)

end

end ProofGap.Exercise878
