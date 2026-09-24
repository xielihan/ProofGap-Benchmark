import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

/-!
# Exercise 24

Semantic formalization of Exercise 24, gaps 1,2,3.
-/

namespace ProofGap.Exercise24

/-- Exercise 24, gap 1. -/
theorem gap1 (x : ℝ) :
    |x| > |x + 1| ↔ x ^ 2 > (x + 1) ^ 2 := by
  constructor <;> intro h
  · nlinarith [sq_abs x, sq_abs (x + 1), abs_nonneg x, abs_nonneg (x + 1)]
  · nlinarith [sq_abs x, sq_abs (x + 1), abs_nonneg x, abs_nonneg (x + 1)]

/-- Exercise 24, gap 2. -/
theorem gap2
    (x : ℝ)
    (h1 : |x| > |x + 1| ↔ x ^ 2 > (x + 1) ^ 2) :
    |x| > |x + 1| ↔ 2 * x + 1 < 0 := by
  rw [h1]
  constructor <;> intro h <;> nlinarith

/-- Exercise 24, gap 3. -/
theorem gap3
    (x : ℝ)
    (h2 : |x| > |x + 1| ↔ 2 * x + 1 < 0) :
    x ∈ {y : ℝ | y < -(1 / 2 : ℝ)} ↔ |x| > |x + 1| := by
  change x < -(1 / 2 : ℝ) ↔ |x| > |x + 1|
  rw [h2]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

end ProofGap.Exercise24
