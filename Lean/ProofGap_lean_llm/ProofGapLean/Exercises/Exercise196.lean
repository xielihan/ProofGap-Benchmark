import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise196

def f (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c
def thirdDiff (a b c x : ℝ) : ℝ :=
  f a b c (x + 3) - 3 * f a b c (x + 2) +
    3 * f a b c (x + 1) - f a b c x

/-- Source: `proof_gap/exercise_196/1.txt`. -/
theorem gap1 (a b c : ℝ) : ∀ x,
    thirdDiff a b c x =
      a * (x + 3) ^ 2 + b * (x + 3) + c -
      3 * (a * (x + 2) ^ 2 + b * (x + 2) + c) +
      3 * (a * (x + 1) ^ 2 + b * (x + 1) + c) -
      (a * x ^ 2 + b * x + c) := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_196/2.txt`; fully expand the finite difference. -/
theorem gap2 (a b c : ℝ) : ∀ x,
    thirdDiff a b c x =
      a * x ^ 2 + 6 * a * x + 9 * a + b * x + 3 * b + c -
      3 * a * x ^ 2 - 12 * a * x - 12 * a - 3 * b * x - 6 * b - 3 * c +
      3 * a * x ^ 2 + 6 * a * x + 3 * a + 3 * b * x + 3 * b + 3 * c -
      a * x ^ 2 - b * x - c := by
  intro x
  unfold thirdDiff f
  ring

/-- Source: `proof_gap/exercise_196/3.txt`. -/
theorem gap3 (a b c : ℝ) : ∀ x, thirdDiff a b c x = 0 := by
  intro x
  unfold thirdDiff f
  ring

/-- Source: `proof_gap/exercise_196/4.txt`; formalize identity as a function equality. -/
theorem gap4 (a b c : ℝ) : thirdDiff a b c = fun _ => 0 := by
  funext x
  exact gap3 a b c x

/-- Source: `proof_gap/exercise_196/5.txt`. -/
theorem gap5 (a b c : ℝ) : thirdDiff a b c = fun _ => 0 := by
  exact gap4 a b c

end ProofGap.Exercise196
