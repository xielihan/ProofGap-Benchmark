import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise862

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.cos (2 * x) - 2 * Real.sin x

/-- Source: `proof_gap/exercise_862/1.txt`. -/
theorem gap1 (x : ℝ) :
    HasDerivAt y (-2 * Real.sin (2 * x) - 2 * Real.cos x) x := by
  have hid : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa only [id_eq, one_mul, mul_comm] using
      (hasDerivAt_id x).mul_const 2
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (2 * t))
        (-2 * Real.sin (2 * x)) x := by
    convert (Real.hasDerivAt_cos (2 * x)).comp x hid using 1 <;> ring
  have hsin :
      HasDerivAt (fun t : ℝ => 2 * Real.sin t) (2 * Real.cos x) x := by
    simpa only [mul_comm] using
      (Real.hasDerivAt_sin x).mul_const 2
  simpa only [y] using hcos.sub hsin

/-- Source: `proof_gap/exercise_862/2.txt`. -/
theorem gap2 (x : ℝ) :
    -2 * Real.sin (2 * x) - 2 * Real.cos x =
      -2 * Real.cos x * (1 + 2 * Real.sin x) := by
  rw [Real.sin_two_mul]
  ring

/-- Source: `proof_gap/exercise_862/3.txt`. -/
theorem gap3 (x : ℝ) :
    HasDerivAt y (-2 * Real.cos x * (1 + 2 * Real.sin x)) x := by
  rw [← gap2 x]
  exact gap1 x

end

end ProofGap.Exercise862
