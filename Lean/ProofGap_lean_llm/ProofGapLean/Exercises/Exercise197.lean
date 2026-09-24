import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise197

def f (a b x : ℝ) : ℝ := a * x + b
def FitsData (a b : ℝ) : Prop := f a b 0 = -2 ∧ f a b 3 = 5

/-- Exercise 197, gap 1. -/
theorem gap1 (a b : ℝ) : f a b 0 = b := by
  simp [f]

/-- Exercise 197, gap 2. -/
theorem gap2 (a b : ℝ) (h : FitsData a b) : b = -2 := by
  simpa [FitsData, f] using h.1

/-- Exercise 197, gap 3. -/
theorem gap3 (a b : ℝ) (h : FitsData a b) : f a b 0 = -2 := by
  exact h.1

/-- Exercise 197, gap 4. -/
theorem gap4 (a b : ℝ) : f a b 3 = 3 * a + b := by
  unfold f
  ring

/-- Exercise 197, gap 5. -/
theorem gap5 (a b : ℝ) (h : FitsData a b) : 3 * a + b = 5 := by
  rw [← gap4]
  exact h.2

/-- Exercise 197, gap 6. -/
theorem gap6 (a b : ℝ) (h : FitsData a b) : f a b 3 = 5 := by
  exact h.2

/-- Exercise 197, gap 7. -/
theorem gap7 (a b : ℝ) (h : FitsData a b) : a = 7 / 3 := by
  have hb := gap2 a b h
  have ha := gap5 a b h
  norm_num at ⊢
  linarith

/-- Exercise 197, gap 8. -/
theorem gap8 (a b : ℝ) (h : FitsData a b) : b = -2 := by
  exact gap2 a b h

/-- Exercise 197, gap 9. -/
theorem gap9 (a b : ℝ) (h : FitsData a b) :
    ∀ x, f a b x = (7 / 3) * x - 2 := by
  intro x
  rw [f, gap7 a b h, gap8 a b h]
  ring

/-- Exercise 197, gap 10. -/
theorem gap10 (a b : ℝ) (h : FitsData a b) : f a b 1 = 1 / 3 := by
  rw [gap9 a b h]
  norm_num

/-- Exercise 197, gap 11. -/
theorem gap11 (a b : ℝ) (h : FitsData a b) : f a b 2 = 8 / 3 := by
  rw [gap9 a b h]
  norm_num

end ProofGap.Exercise197
