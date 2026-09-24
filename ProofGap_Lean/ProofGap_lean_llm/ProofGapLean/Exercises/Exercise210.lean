import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise210

def f (x : ℝ) : ℝ := x ^ 2 - 5 * x + 6

/-- Exercise 210, gap 1. -/
theorem gap1 : ∀ x, f (x + 1) = (x + 1) ^ 2 - 5 * (x + 1) + 6 := by
  intro x
  rfl

/-- Exercise 210, gap 2. -/
theorem gap2 : ∀ x, f x = x ^ 2 - 5 * x + 6 := by
  intro x
  rfl

end ProofGap.Exercise210
