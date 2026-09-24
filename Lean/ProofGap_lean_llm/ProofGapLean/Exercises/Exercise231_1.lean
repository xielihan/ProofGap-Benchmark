import ProofGapLean.Prelude.Core
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise231_1

def f (x : ℝ) : ℝ := 3 * x - x ^ 3

/-- Source: `proof_gap/exercise_231_1/1.txt`. -/
theorem gap1 : ∀ x, f (-x) = -3 * x + x ^ 3 := by
  intro x
  simp [f]
  ring

/-- Source: `proof_gap/exercise_231_1/2.txt`. -/
theorem gap2 : ∀ x, -3 * x + x ^ 3 = -f x := by
  intro x
  simp [f]
  ring

/-- Source: `proof_gap/exercise_231_1/3.txt`. -/
theorem gap3 : ∀ x, f (-x) = -f x := by
  intro x
  rw [gap1, gap2]

/-- Source: `proof_gap/exercise_231_1/4.txt`. -/
theorem gap4 : Function.Odd f := by
  intro x
  exact gap3 x

end ProofGap.Exercise231_1
