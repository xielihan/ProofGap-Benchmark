import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise830

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2 * Real.sin (x - 2)

/-- Source: `proof_gap/exercise_830/1.txt`. -/
theorem gap1 (x : ℝ) :
    HasDerivAt f
      (2 * x * Real.sin (x - 2) + x ^ 2 * Real.cos (x - 2)) x := by
  unfold f
  convert
    ((hasDerivAt_id x).pow 2).mul
      ((Real.hasDerivAt_sin (x - 2)).comp x
        ((hasDerivAt_id x).sub (hasDerivAt_const x 2))) using 1 <;>
    norm_num <;> ring

/-- Source: `proof_gap/exercise_830/2.txt`. -/
theorem gap2 : HasDerivAt f 4 2 := by
  convert gap1 (x := (2 : ℝ)) using 1 <;> norm_num

end

end ProofGap.Exercise830
