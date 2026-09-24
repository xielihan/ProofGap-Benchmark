import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise195_1

noncomputable section

def f (a b x : ℝ) : ℝ := a * x + b
def φ (a b h x : ℝ) : ℝ := (f a b (x + h) - f a b x) / h

/-- Source: `proof_gap/exercise_195_1/1.txt`; h≠0 is required. -/
theorem gap1 (a b h : ℝ) (hh : h ≠ 0) :
    ∀ x, φ a b h x = (a * (x + h) + b - (a * x + b)) / h := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_195_1/2.txt`. -/
theorem gap2 (a b h : ℝ) (hh : h ≠ 0) :
    ∀ x, (a * (x + h) + b - (a * x + b)) / h = a := by
  intro x
  field_simp
  ring

/-- Source: `proof_gap/exercise_195_1/3.txt`. -/
theorem gap3 (a b h : ℝ) (hh : h ≠ 0) : ∀ x, φ a b h x = a := by
  intro x
  exact gap2 a b h hh x

end

end ProofGap.Exercise195_1
