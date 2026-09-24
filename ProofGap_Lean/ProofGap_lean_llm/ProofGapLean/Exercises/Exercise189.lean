import ProofGapLean.Prelude.Core
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise189

def f (x : ℝ) : ℝ := x ^ 4 - 6 * x ^ 3 + 11 * x ^ 2 - 6 * x

/-- Exercise 189, gap 1. -/
theorem gap1 : ∀ x : ℝ, f x = x * (x - 1) * (x - 2) * (x - 3) := by
  intro x
  unfold f
  ring

/-- Exercise 189, gap 2. -/
theorem gap2 : f 0 = f 1 := by
  norm_num [f]

/-- Exercise 189, gap 3. -/
theorem gap3 : f 1 = f 2 := by
  norm_num [f]

/-- Exercise 189, gap 4. -/
theorem gap4 : f 2 = f 3 := by
  norm_num [f]

/-- Exercise 189, gap 5. -/
theorem gap5 : f 3 = 0 := by
  norm_num [f]

/-- Exercise 189, gap 6. -/
theorem gap6 : f 0 = 0 := by
  norm_num [f]

/-- Exercise 189, gap 7. -/
theorem gap7 : f 4 = 24 := by
  norm_num [f]

end ProofGap.Exercise189
