import ProofGapLean.Prelude.Core
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise231_1

def f (x : ℝ) : ℝ := 3 * x - x ^ 3

/-- Exercise 231_1, gap 1. -/
theorem gap1 : ∀ x, f (-x) = -3 * x + x ^ 3 := by
  intro x
  simp [f]
  ring

/-- Exercise 231_1, gap 2. -/
theorem gap2 : ∀ x, -3 * x + x ^ 3 = -f x := by
  intro x
  simp [f]
  ring

/-- Exercise 231_1, gap 3. -/
theorem gap3 : ∀ x, f (-x) = -f x := by
  intro x
  rw [gap1, gap2]

/-- Exercise 231_1, gap 4. -/
theorem gap4 : Function.Odd f := by
  intro x
  exact gap3 x

end ProofGap.Exercise231_1
