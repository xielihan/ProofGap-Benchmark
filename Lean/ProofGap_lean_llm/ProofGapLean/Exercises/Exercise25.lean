import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

/-!
# Exercise 25

Semantic formalization of `proof_gap/exercise_25/{1,2,3}.txt`.
-/

namespace ProofGap.Exercise25

/-- Source: `proof_gap/exercise_25/1.txt`. -/
theorem gap1 (x : ℝ) :
    |2 * x - 1| < |x - 1| ↔
      (2 * x - 1) ^ 2 < (x - 1) ^ 2 := by
  constructor <;> intro h
  · nlinarith [sq_abs (2 * x - 1), sq_abs (x - 1),
      abs_nonneg (2 * x - 1), abs_nonneg (x - 1)]
  · nlinarith [sq_abs (2 * x - 1), sq_abs (x - 1),
      abs_nonneg (2 * x - 1), abs_nonneg (x - 1)]

/-- Source: `proof_gap/exercise_25/2.txt`. -/
theorem gap2
    (x : ℝ)
    (h1 : |2 * x - 1| < |x - 1| ↔
      (2 * x - 1) ^ 2 < (x - 1) ^ 2) :
    |2 * x - 1| < |x - 1| ↔ 3 * x ^ 2 - 2 * x < 0 := by
  rw [h1]
  constructor <;> intro h <;> nlinarith

/-- Source: `proof_gap/exercise_25/3.txt`. -/
theorem gap3
    (x : ℝ)
    (h2 : |2 * x - 1| < |x - 1| ↔ 3 * x ^ 2 - 2 * x < 0) :
    x ∈ {y : ℝ | 0 < y ∧ y < (2 / 3 : ℝ)} ↔
      |2 * x - 1| < |x - 1| := by
  change (0 < x ∧ x < (2 / 3 : ℝ)) ↔ |2 * x - 1| < |x - 1|
  rw [h2]
  constructor
  · rintro ⟨hx0, hx23⟩
    nlinarith
  · intro h
    constructor <;> nlinarith

end ProofGap.Exercise25
