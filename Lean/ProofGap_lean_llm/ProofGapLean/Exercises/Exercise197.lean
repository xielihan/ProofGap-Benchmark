import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise197

def f (a b x : ℝ) : ℝ := a * x + b
def FitsData (a b : ℝ) : Prop := f a b 0 = -2 ∧ f a b 3 = 5

/-- Source: `proof_gap/exercise_197/1.txt`. -/
theorem gap1 (a b : ℝ) : f a b 0 = b := by
  simp [f]

/-- Source: `proof_gap/exercise_197/2.txt`. -/
theorem gap2 (a b : ℝ) (h : FitsData a b) : b = -2 := by
  simpa [FitsData, f] using h.1

/-- Source: `proof_gap/exercise_197/3.txt`. -/
theorem gap3 (a b : ℝ) (h : FitsData a b) : f a b 0 = -2 := by
  exact h.1

/-- Source: `proof_gap/exercise_197/4.txt`. -/
theorem gap4 (a b : ℝ) : f a b 3 = 3 * a + b := by
  unfold f
  ring

/-- Source: `proof_gap/exercise_197/5.txt`. -/
theorem gap5 (a b : ℝ) (h : FitsData a b) : 3 * a + b = 5 := by
  rw [← gap4]
  exact h.2

/-- Source: `proof_gap/exercise_197/6.txt`. -/
theorem gap6 (a b : ℝ) (h : FitsData a b) : f a b 3 = 5 := by
  exact h.2

/-- Source: `proof_gap/exercise_197/7.txt`. -/
theorem gap7 (a b : ℝ) (h : FitsData a b) : a = 7 / 3 := by
  have hb := gap2 a b h
  have ha := gap5 a b h
  norm_num at ⊢
  linarith

/-- Source: `proof_gap/exercise_197/8.txt`. -/
theorem gap8 (a b : ℝ) (h : FitsData a b) : b = -2 := by
  exact gap2 a b h

/-- Source: `proof_gap/exercise_197/9.txt`. -/
theorem gap9 (a b : ℝ) (h : FitsData a b) :
    ∀ x, f a b x = (7 / 3) * x - 2 := by
  intro x
  rw [f, gap7 a b h, gap8 a b h]
  ring

/-- Source: `proof_gap/exercise_197/10.txt`. -/
theorem gap10 (a b : ℝ) (h : FitsData a b) : f a b 1 = 1 / 3 := by
  rw [gap9 a b h]
  norm_num

/-- Source: `proof_gap/exercise_197/11.txt`. -/
theorem gap11 (a b : ℝ) (h : FitsData a b) : f a b 2 = 8 / 3 := by
  rw [gap9 a b h]
  norm_num

end ProofGap.Exercise197
