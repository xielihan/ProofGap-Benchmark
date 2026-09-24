import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise864

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.sin (Real.cos x ^ 2) * Real.cos (Real.sin x ^ 2)

/-- Source: `proof_gap/exercise_864/1.txt`. -/
theorem gap1 (x : ℝ) :
    HasDerivAt y
      (-2 * Real.sin x * Real.cos x * Real.cos (Real.cos x ^ 2) *
          Real.cos (Real.sin x ^ 2) -
        2 * Real.sin x * Real.cos x * Real.sin (Real.cos x ^ 2) *
          Real.sin (Real.sin x ^ 2)) x := by
  unfold y
  have h₁ :
      HasDerivAt (fun t : ℝ => Real.sin (Real.cos t ^ 2))
        (-2 * Real.sin x * Real.cos x * Real.cos (Real.cos x ^ 2)) x := by
    convert
      (Real.hasDerivAt_sin (Real.cos x ^ 2)).comp x
        ((Real.hasDerivAt_cos x).pow 2) using 1 <;>
      ring
  have h₂ :
      HasDerivAt (fun t : ℝ => Real.cos (Real.sin t ^ 2))
        (-2 * Real.sin x * Real.cos x * Real.sin (Real.sin x ^ 2)) x := by
    convert
      (Real.hasDerivAt_cos (Real.sin x ^ 2)).comp x
        ((Real.hasDerivAt_sin x).pow 2) using 1 <;>
      ring
  convert h₁.mul h₂ using 1 <;>
    ring

/-- Source: `proof_gap/exercise_864/2.txt`. -/
theorem gap2 (x : ℝ) :
    HasDerivAt y
      (-Real.sin (2 * x) *
        (Real.cos (Real.cos x ^ 2) * Real.cos (Real.sin x ^ 2) +
          Real.sin (Real.cos x ^ 2) * Real.sin (Real.sin x ^ 2))) x := by
  convert gap1 x using 1 <;>
    rw [Real.sin_two_mul] <;>
    ring

/-- Source: `proof_gap/exercise_864/3.txt`. -/
theorem gap3 (x : ℝ) :
    HasDerivAt y
      (-Real.sin (2 * x) * Real.cos (Real.cos x ^ 2 - Real.sin x ^ 2)) x := by
  simpa only [Real.cos_sub] using gap2 x

/-- Source: `proof_gap/exercise_864/4.txt`. -/
theorem gap4 (x : ℝ) :
    HasDerivAt y (-Real.sin (2 * x) * Real.cos (Real.cos (2 * x))) x := by
  have h : Real.cos x ^ 2 - Real.sin x ^ 2 = Real.cos (2 * x) := by
    rw [show (2 * x : ℝ) = x + x by ring, Real.cos_add]
    ring
  simpa only [h] using gap3 x

end

end ProofGap.Exercise864
