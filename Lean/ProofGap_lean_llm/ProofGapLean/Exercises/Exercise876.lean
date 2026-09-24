import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise876

noncomputable section

def y (x : ℝ) : ℝ := Real.exp (-x ^ 2)

theorem gap1 (x : ℝ) :
    deriv y x = -2 * x * Real.exp (-x ^ 2) := by
  unfold y
  have h_inner : HasDerivAt (fun z : ℝ => -(z * z)) (-2 * x) x := by
    convert (hasDerivAt_id' x).mul (hasDerivAt_id' x) |>.neg using 1 <;> ring
  have h_inner' : HasDerivAt (fun z : ℝ => -z ^ 2) (-2 * x) x := by
    simpa [pow_two] using h_inner
  convert ((Real.hasDerivAt_exp (-x ^ 2)).comp x h_inner').deriv using 1 <;> ring

end

end ProofGap.Exercise876
