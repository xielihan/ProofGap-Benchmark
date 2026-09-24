import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise195_2

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2
def φ (h x : ℝ) : ℝ := (f (x + h) - f x) / h

/-- Source: `proof_gap/exercise_195_2/1.txt`; h≠0 is required. -/
theorem gap1 (h : ℝ) (hh : h ≠ 0) :
    ∀ x, φ h x = ((x + h) ^ 2 - x ^ 2) / h := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_195_2/2.txt`. -/
theorem gap2 (h : ℝ) (hh : h ≠ 0) :
    ∀ x, ((x + h) ^ 2 - x ^ 2) / h = 2 * x + h := by
  intro x
  field_simp
  ring

/-- Source: `proof_gap/exercise_195_2/3.txt`. -/
theorem gap3 (h : ℝ) (hh : h ≠ 0) : ∀ x, φ h x = 2 * x + h := by
  intro x
  exact gap2 h hh x

end

end ProofGap.Exercise195_2
