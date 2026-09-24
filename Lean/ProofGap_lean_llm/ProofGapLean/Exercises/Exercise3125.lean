import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3125

noncomputable section

def P (x : ℝ) : ℝ :=
  (x * (x - 1 / 2) * (x ^ 2 - 1)) /
      ((-1 / 2 : ℝ) * (-1) * (1 / 2) * (-3 / 2)) * (1 / 2) +
    (x * (x + 1 / 2) * (x ^ 2 - 1)) /
      ((1 / 2 : ℝ) * 1 * (3 / 2) * (-1 / 2)) * (1 / 2) +
    (x * (x - 1) * (x ^ 2 - 1 / 4)) /
      ((-1 : ℝ) * (-1 / 2) * (-3 / 2) * (-2)) +
    (x * (x + 1) * (x ^ 2 - 1 / 4)) /
      ((1 : ℝ) * (3 / 2) * (1 / 2) * 2)

/--
Source: `proof_gap/exercise_3125/1.txt`; define `P` as the Lagrange
interpolant of `|x|` at `0, ±1/2, ±1`.
-/
theorem gap1 :
    ∀ x : ℝ,
      P x =
        (x * (x - 1 / 2) * (x ^ 2 - 1)) /
            ((-1 / 2 : ℝ) * (-1) * (1 / 2) * (-3 / 2)) * (1 / 2) +
          (x * (x + 1 / 2) * (x ^ 2 - 1)) /
            ((1 / 2 : ℝ) * 1 * (3 / 2) * (-1 / 2)) * (1 / 2) +
          (x * (x - 1) * (x ^ 2 - 1 / 4)) /
            ((-1 : ℝ) * (-1 / 2) * (-3 / 2) * (-2)) +
          (x * (x + 1) * (x ^ 2 - 1 / 4)) /
            ((1 : ℝ) * (3 / 2) * (1 / 2) * 2) := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_3125/2.txt`; simplify the fixed interpolant. -/
theorem gap2 :
    ∀ x : ℝ, P x = x ^ 2 / 3 * (7 - 4 * x ^ 2) := by
  intro x
  unfold P
  ring

end

end ProofGap.Exercise3125
