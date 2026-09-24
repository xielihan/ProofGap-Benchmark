import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

/-!
# Exercise 23

Semantic formalization of `proof_gap/exercise_23/{1,2,3}.txt`.
-/

namespace ProofGap.Exercise23

/-- Source: `proof_gap/exercise_23/1.txt`. -/
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

/-- Source: `proof_gap/exercise_23/2.txt`. -/
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

/-- Source: `proof_gap/exercise_23/3.txt`. -/
theorem gap3
    (x : ℝ)
    (h2 : |x - 2| ≥ 10 ↔ x ≥ 12 ∨ x ≤ -8) :
    x ∈ {y : ℝ | y ≥ 12 ∨ y ≤ -8} ↔ |x - 2| ≥ 10 := by
  change (x ≥ 12 ∨ x ≤ -8) ↔ |x - 2| ≥ 10
  exact h2.symm

end ProofGap.Exercise23
