import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise198

def f (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c
def FitsData (a b c : ℝ) : Prop :=
  f a b c (-2) = 0 ∧ f a b c 0 = 1 ∧ f a b c 1 = 5

/-- Source: `proof_gap/exercise_198/1.txt`. -/
theorem gap1 (a b c : ℝ) : f a b c (-2) = 4 * a - 2 * b + c := by
  unfold f
  ring

/-- Source: `proof_gap/exercise_198/2.txt`. -/
theorem gap2 (a b c : ℝ) (h : FitsData a b c) : 4 * a - 2 * b + c = 0 := by
  rw [← gap1]
  exact h.1

/-- Source: `proof_gap/exercise_198/3.txt`. -/
theorem gap3 (a b c : ℝ) (h : FitsData a b c) : f a b c (-2) = 0 := by
  exact h.1

/-- Source: `proof_gap/exercise_198/4.txt`. -/
theorem gap4 (a b c : ℝ) : f a b c 0 = c := by
  simp [f]

/-- Source: `proof_gap/exercise_198/5.txt`. -/
theorem gap5 (a b c : ℝ) (h : FitsData a b c) : c = 1 := by
  simpa [FitsData, f] using h.2.1

/-- Source: `proof_gap/exercise_198/6.txt`. -/
theorem gap6 (a b c : ℝ) (h : FitsData a b c) : f a b c 0 = 1 := by
  exact h.2.1

/-- Source: `proof_gap/exercise_198/7.txt`. -/
theorem gap7 (a b c : ℝ) : f a b c 1 = a + b + c := by
  unfold f
  ring

/-- Source: `proof_gap/exercise_198/8.txt`. -/
theorem gap8 (a b c : ℝ) (h : FitsData a b c) : a + b + c = 5 := by
  rw [← gap7]
  exact h.2.2

/-- Source: `proof_gap/exercise_198/9.txt`. -/
theorem gap9 (a b c : ℝ) (h : FitsData a b c) : f a b c 1 = 5 := by
  exact h.2.2

/-- Source: `proof_gap/exercise_198/10.txt`. -/
theorem gap10 (a b c : ℝ) (h : FitsData a b c) : a = 7 / 6 := by
  have h₁ := gap2 a b c h
  have h₂ := gap5 a b c h
  have h₃ := gap8 a b c h
  norm_num at ⊢
  linarith

/-- Source: `proof_gap/exercise_198/11.txt`. -/
theorem gap11 (a b c : ℝ) (h : FitsData a b c) : b = 17 / 6 := by
  have h₁ := gap2 a b c h
  have h₂ := gap5 a b c h
  have h₃ := gap8 a b c h
  norm_num at ⊢
  linarith

/-- Source: `proof_gap/exercise_198/12.txt`. -/
theorem gap12 (a b c : ℝ) (h : FitsData a b c) : c = 1 := by
  exact gap5 a b c h

/-- Source: `proof_gap/exercise_198/13.txt`. -/
theorem gap13 (a b c : ℝ) (h : FitsData a b c) :
    ∀ x, f a b c x = (7 / 6) * x ^ 2 + (17 / 6) * x + 1 := by
  intro x
  rw [f, gap10 a b c h, gap11 a b c h, gap12 a b c h]

/-- Source: `proof_gap/exercise_198/14.txt`. -/
theorem gap14 (a b c : ℝ) (h : FitsData a b c) : f a b c (-1) = -2 / 3 := by
  rw [gap13 a b c h]
  norm_num

/-- Source: `proof_gap/exercise_198/15.txt`. -/
theorem gap15 (a b c : ℝ) (h : FitsData a b c) : f a b c (1 / 2) = 65 / 24 := by
  rw [gap13 a b c h]
  norm_num

end ProofGap.Exercise198
