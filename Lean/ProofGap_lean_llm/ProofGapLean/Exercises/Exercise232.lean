import ProofGapLean.Prelude.Core
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise232

noncomputable section

def evenPart (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x + f (-x)) / 2
def oddPart (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x - f (-x)) / 2

/-- Source: `proof_gap/exercise_232/1.txt`. -/
theorem gap1 (f : ℝ → ℝ) : ∀ x,
    f x = (f x + f (-x)) / 2 + (f x - f (-x)) / 2 := by
  intro x
  ring

/-- Source: `proof_gap/exercise_232/2.txt`. -/
theorem gap2 (f : ℝ → ℝ) : Function.Even (evenPart f) := by
  intro x
  unfold evenPart
  rw [neg_neg]
  ring

/-- Source: `proof_gap/exercise_232/3.txt`. -/
theorem gap3 (f : ℝ → ℝ) : Function.Odd (oddPart f) := by
  intro x
  unfold oddPart
  rw [neg_neg]
  ring

/-- Source: `proof_gap/exercise_232/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) : ∀ x,
    f x = evenPart f x + oddPart f x := by
  intro x
  simpa [evenPart, oddPart] using gap1 f x

/-- Source: `proof_gap/exercise_232/5.txt`; move the function witnesses outside the point quantifier. -/
theorem gap5 (f : ℝ → ℝ) :
    ∃ g h : ℝ → ℝ,
      Function.Even g ∧ Function.Odd h ∧ ∀ x, f x = g x + h x := by
  refine ⟨evenPart f, oddPart f, gap2 f, gap3 f, ?_⟩
  exact gap4 f

end

end ProofGap.Exercise232
