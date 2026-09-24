import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise210

def f (x : ℝ) : ℝ := x ^ 2 - 5 * x + 6

/-- Source: `proof_gap/exercise_210/1.txt`. -/
theorem gap1 : ∀ x, f (x + 1) = (x + 1) ^ 2 - 5 * (x + 1) + 6 := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_210/2.txt`. -/
theorem gap2 : ∀ x, f x = x ^ 2 - 5 * x + 6 := by
  intro x
  rfl

end ProofGap.Exercise210
