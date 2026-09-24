import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise866

noncomputable section

def y (x : ℝ) : ℝ := Real.sin (Real.sin (Real.sin x))

/-- Source: `proof_gap/exercise_866/1.txt`. -/
theorem gap1 (x : ℝ) :
    deriv y x =
      Real.cos x * Real.cos (Real.sin x) *
        Real.cos (Real.sin (Real.sin x)) := by
  change deriv (fun z : ℝ => Real.sin (Real.sin (Real.sin z))) x = _
  have h₂ :
      HasDerivAt (fun z : ℝ => Real.sin (Real.sin z))
        (Real.cos (Real.sin x) * Real.cos x) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (Real.sin x)).comp x (Real.hasDerivAt_sin x)
  have h₃ :
      HasDerivAt (fun z : ℝ => Real.sin (Real.sin (Real.sin z)))
        (Real.cos (Real.sin (Real.sin x)) *
          (Real.cos (Real.sin x) * Real.cos x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (Real.sin (Real.sin x))).comp x h₂
  rw [h₃.deriv]
  ring

end

end ProofGap.Exercise866
