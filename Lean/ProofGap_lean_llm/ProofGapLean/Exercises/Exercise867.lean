import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise867

noncomputable section

def y (x : ℝ) : ℝ := Real.sin x ^ 2 / Real.sin (x ^ 2)

/-- Source: `proof_gap/exercise_867/1.txt`; restrict to the domain of the
quotient. -/
theorem gap1 (x : ℝ) (hden : Real.sin (x ^ 2) ≠ 0) :
    deriv y x =
      (2 * Real.sin x *
        (Real.cos x * Real.sin (x ^ 2) -
          x * Real.sin x * Real.cos (x ^ 2))) /
        Real.sin (x ^ 2) ^ 2 := by
  have hnum :
      HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
        (2 * Real.sin x * Real.cos x) x := by
    convert (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_sin x) using 1 <;>
      first
      | (funext t; simp [pow_two])
      | ring
  have hx2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1 <;>
      first
      | (funext t; simp [pow_two])
      | (simp <;> ring)
  have hden' :
      HasDerivAt (fun t : ℝ => Real.sin (t ^ 2))
        (2 * x * Real.cos (x ^ 2)) x := by
    convert (Real.hasDerivAt_sin (x ^ 2)).comp x hx2 using 1 <;>
      first
      | (funext t; simp [Function.comp_def, pow_two])
      | ring
  unfold y
  convert (hnum.div hden' hden).deriv using 1 <;>
    first
    | (funext t; simp [pow_two])
    | ring

end

end ProofGap.Exercise867
