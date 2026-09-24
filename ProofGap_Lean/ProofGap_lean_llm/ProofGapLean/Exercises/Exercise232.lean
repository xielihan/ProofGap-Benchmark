import ProofGapLean.Prelude.Core
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise232

noncomputable section

def evenPart (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x + f (-x)) / 2
def oddPart (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x - f (-x)) / 2

/-- Exercise 232, gap 1. -/
theorem gap1 (f : ℝ → ℝ) : ∀ x,
    f x = (f x + f (-x)) / 2 + (f x - f (-x)) / 2 := by
  intro x
  ring

/-- Exercise 232, gap 2. -/
theorem gap2 (f : ℝ → ℝ) : Function.Even (evenPart f) := by
  intro x
  unfold evenPart
  rw [neg_neg]
  ring

/-- Exercise 232, gap 3. -/
theorem gap3 (f : ℝ → ℝ) : Function.Odd (oddPart f) := by
  intro x
  unfold oddPart
  rw [neg_neg]
  ring

/-- Exercise 232, gap 4. -/
theorem gap4 (f : ℝ → ℝ) : ∀ x,
    f x = evenPart f x + oddPart f x := by
  intro x
  simpa [evenPart, oddPart] using gap1 f x

/-- Exercise 232, gap 5; move the function witnesses outside the point quantifier. -/
theorem gap5 (f : ℝ → ℝ) :
    ∃ g h : ℝ → ℝ,
      Function.Even g ∧ Function.Odd h ∧ ∀ x, f x = g x + h x := by
  refine ⟨evenPart f, oddPart f, gap2 f, gap3 f, ?_⟩
  exact gap4 f

end

end ProofGap.Exercise232
