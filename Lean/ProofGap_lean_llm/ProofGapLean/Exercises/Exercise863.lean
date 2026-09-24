import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise863

noncomputable section

def y (x : ℝ) : ℝ :=
  (2 - x ^ 2) * Real.cos x + 2 * x * Real.sin x

/-- Source: `proof_gap/exercise_863/1.txt`. -/
theorem gap1 (x : ℝ) :
    HasDerivAt y
      (-2 * x * Real.cos x - (2 - x ^ 2) * Real.sin x +
        2 * Real.sin x + 2 * x * Real.cos x) x := by
  unfold y
  convert
    (((hasDerivAt_const x (2 : ℝ)).sub ((hasDerivAt_id x).pow 2)).mul
      (Real.hasDerivAt_cos x)).add
      (((hasDerivAt_id x).const_mul 2).mul (Real.hasDerivAt_sin x))
    using 1 <;> simp <;> ring

/-- Source: `proof_gap/exercise_863/2.txt`. -/
theorem gap2 (x : ℝ) :
    -2 * x * Real.cos x - (2 - x ^ 2) * Real.sin x +
          2 * Real.sin x + 2 * x * Real.cos x =
      x ^ 2 * Real.sin x := by
  ring

/-- Source: `proof_gap/exercise_863/3.txt`. -/
theorem gap3 (x : ℝ) :
    HasDerivAt y (x ^ 2 * Real.sin x) x := by
  convert gap1 x using 1
  exact (gap2 x).symm

end

end ProofGap.Exercise863
