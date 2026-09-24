import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise221_1

def f (a b x : ℝ) : ℝ := a * x + b

/-- Source: `proof_gap/exercise_221_1/1.txt`. -/
theorem gap1 (a b : ℝ) : ∀ x₁ x₂, x₁ < x₂ →
    f a b x₂ - f a b x₁ = a * (x₂ - x₁) := by
  intro x₁ x₂ hlt
  simp only [f]
  ring

/-- Source: `proof_gap/exercise_221_1/2.txt`. -/
theorem gap2 (a b : ℝ) : ∀ x₁ x₂, x₁ < x₂ → 0 < a →
    0 < f a b x₂ - f a b x₁ := by
  intro x₁ x₂ hlt ha
  rw [gap1 a b x₁ x₂ hlt]
  exact mul_pos ha (sub_pos.mpr hlt)

/-- Source: `proof_gap/exercise_221_1/3.txt`. -/
theorem gap3 (a b : ℝ) : ∀ x₁ x₂, x₁ < x₂ → a < 0 →
    f a b x₂ - f a b x₁ < 0 := by
  intro x₁ x₂ hlt ha
  rw [gap1 a b x₁ x₂ hlt]
  exact mul_neg_of_neg_of_pos ha (sub_pos.mpr hlt)

/-- Source: `proof_gap/exercise_221_1/4.txt`. -/
theorem gap4 (a b : ℝ) (ha : 0 < a) : StrictMono (f a b) := by
  intro x₁ x₂ hlt
  have := gap2 a b x₁ x₂ hlt ha
  linarith

/-- Source: `proof_gap/exercise_221_1/5.txt`. -/
theorem gap5 (a b : ℝ) (ha : a < 0) : StrictAnti (f a b) := by
  intro x₁ x₂ hlt
  have := gap3 a b x₁ x₂ hlt ha
  linarith

end ProofGap.Exercise221_1
