import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1665

noncomputable section

def integrand (x : ℝ) : ℝ := Real.exp (-x) + Real.exp (-2 * x)
def primitive (x : ℝ) : ℝ := -(Real.exp (-x) + (1 / 2 : ℝ) * Real.exp (-2 * x))

theorem gap1 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  unfold primitive integrand
  have h₁ : HasDerivAt (fun y : ℝ => Real.exp (-y))
      (-Real.exp (-x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)
  have hlinear : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hinner : HasDerivAt (fun y : ℝ => -2 * y) (-2) x := by
    simpa only [Pi.neg_apply, neg_mul] using hlinear.neg
  have h₂ : HasDerivAt (fun y : ℝ => Real.exp (-2 * y))
      (-2 * Real.exp (-2 * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (-2 * x)).comp x hinner
  have hc : HasDerivAt
      (fun y : ℝ => (1 / 2 : ℝ) * Real.exp (-2 * y))
      ((1 / 2 : ℝ) * (-2 * Real.exp (-2 * x))) x := by
    simpa using (hasDerivAt_const x (1 / 2 : ℝ)).mul h₂
  convert (h₁.add hc).neg using 1 <;> ring

end

end ProofGap.Exercise1665
