import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise199

def f (a b c d x : ℝ) : ℝ := a * x ^ 3 + b * x ^ 2 + c * x + d
def FitsData (a b c d : ℝ) : Prop :=
  f a b c d (-1) = 0 ∧ f a b c d 0 = 2 ∧
  f a b c d 1 = -3 ∧ f a b c d 2 = 5

/-- Exercise 199, gap 1; remove the malformed universal equivalence. -/
theorem gap1 (a b c d : ℝ) : f a b c d (-1) = -a + b - c + d := by
  unfold f
  ring

/-- Exercise 199, gap 2. -/
theorem gap2 (a b c d : ℝ) (h : FitsData a b c d) : -a + b - c + d = 0 := by
  rw [← gap1]
  exact h.1

/-- Exercise 199, gap 3. -/
theorem gap3 (a b c d : ℝ) (h : FitsData a b c d) : f a b c d (-1) = 0 := by
  exact h.1

/-- Exercise 199, gap 4. -/
theorem gap4 (a b c d : ℝ) : f a b c d 0 = d := by
  simp [f]

/-- Exercise 199, gap 5. -/
theorem gap5 (a b c d : ℝ) (h : FitsData a b c d) : d = 2 := by
  simpa [FitsData, f] using h.2.1

/-- Exercise 199, gap 6. -/
theorem gap6 (a b c d : ℝ) (h : FitsData a b c d) : f a b c d 0 = 2 := by
  exact h.2.1

/-- Exercise 199, gap 7. -/
theorem gap7 (a b c d : ℝ) : f a b c d 1 = a + b + c + d := by
  unfold f
  ring

/-- Exercise 199, gap 8. -/
theorem gap8 (a b c d : ℝ) (h : FitsData a b c d) : a + b + c + d = -3 := by
  rw [← gap7]
  exact h.2.2.1

/-- Exercise 199, gap 9. -/
theorem gap9 (a b c d : ℝ) (h : FitsData a b c d) : f a b c d 1 = -3 := by
  exact h.2.2.1

/-- Exercise 199, gap 10. -/
theorem gap10 (a b c d : ℝ) : f a b c d 2 = 8 * a + 4 * b + 2 * c + d := by
  unfold f
  ring

/-- Exercise 199, gap 11. -/
theorem gap11 (a b c d : ℝ) (h : FitsData a b c d) :
    8 * a + 4 * b + 2 * c + d = 5 := by
  rw [← gap10]
  exact h.2.2.2

/-- Exercise 199, gap 12. -/
theorem gap12 (a b c d : ℝ) (h : FitsData a b c d) : f a b c d 2 = 5 := by
  exact h.2.2.2

/-- Exercise 199, gap 13. -/
theorem gap13 (a b c d : ℝ) (h : FitsData a b c d) : a = 10 / 3 := by
  have h₁ := gap2 a b c d h
  have h₂ := gap5 a b c d h
  have h₃ := gap8 a b c d h
  have h₄ := gap11 a b c d h
  norm_num at ⊢
  linarith

/-- Exercise 199, gap 14. -/
theorem gap14 (a b c d : ℝ) (h : FitsData a b c d) : b = -7 / 2 := by
  have h₁ := gap2 a b c d h
  have h₂ := gap5 a b c d h
  have h₃ := gap8 a b c d h
  have h₄ := gap11 a b c d h
  norm_num at ⊢
  linarith

/-- Exercise 199, gap 15. -/
theorem gap15 (a b c d : ℝ) (h : FitsData a b c d) : c = -29 / 6 := by
  have h₁ := gap2 a b c d h
  have h₂ := gap5 a b c d h
  have h₃ := gap8 a b c d h
  have h₄ := gap11 a b c d h
  norm_num at ⊢
  linarith

/-- Exercise 199, gap 16. -/
theorem gap16 (a b c d : ℝ) (h : FitsData a b c d) : d = 2 := by
  exact gap5 a b c d h

/-- Exercise 199, gap 17. -/
theorem gap17 (a b c d : ℝ) (h : FitsData a b c d) :
    ∀ x, f a b c d x = (10 / 3) * x ^ 3 - (7 / 2) * x ^ 2 - (29 / 6) * x + 2 := by
  intro x
  rw [f, gap13 a b c d h, gap14 a b c d h,
    gap15 a b c d h, gap16 a b c d h]
  ring

/-- Exercise 199, gap 18; state the converse without a malformed singleton tuple binder. -/
theorem gap18 :
    FitsData (10 / 3) (-7 / 2) (-29 / 6) 2 := by
  norm_num [FitsData, f]

end ProofGap.Exercise199
