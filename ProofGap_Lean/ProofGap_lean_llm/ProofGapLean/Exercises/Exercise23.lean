import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

/-!
# Exercise 23

Semantic formalization of Exercise 23, gaps 1,2,3.
-/

namespace ProofGap.Exercise23

/-- Exercise 23, gap 1. -/
theorem gap1 (x : ℝ) :
    |x - 2| ≥ 10 ↔ x - 2 ≥ 10 ∨ x - 2 ≤ -10 := by
  constructor
  · intro h
    rcases le_total 0 (x - 2) with hnonneg | hnonpos
    · left
      rw [abs_of_nonneg hnonneg] at h
      exact h
    · right
      rw [abs_of_nonpos hnonpos] at h
      linarith
  · rintro (h | h)
    · rw [abs_of_nonneg (by linarith)]
      exact h
    · rw [abs_of_nonpos (by linarith)]
      linarith

/-- Exercise 23, gap 2. -/
theorem gap2
    (x : ℝ)
    (h1 : |x - 2| ≥ 10 ↔ x - 2 ≥ 10 ∨ x - 2 ≤ -10) :
    |x - 2| ≥ 10 ↔ x ≥ 12 ∨ x ≤ -8 := by
  rw [h1]
  constructor <;> rintro (h | h)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Exercise 23, gap 3. -/
theorem gap3
    (x : ℝ)
    (h2 : |x - 2| ≥ 10 ↔ x ≥ 12 ∨ x ≤ -8) :
    x ∈ {y : ℝ | y ≥ 12 ∨ y ≤ -8} ↔ |x - 2| ≥ 10 := by
  change (x ≥ 12 ∨ x ≤ -8) ↔ |x - 2| ≥ 10
  exact h2.symm

end ProofGap.Exercise23
