import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise221_1

def f (a b x : ℝ) : ℝ := a * x + b

/-- Exercise 221_1, gap 1. -/
theorem gap1 (a b : ℝ) : ∀ x₁ x₂, x₁ < x₂ →
    f a b x₂ - f a b x₁ = a * (x₂ - x₁) := by
  intro x₁ x₂ hlt
  simp only [f]
  ring

/-- Exercise 221_1, gap 2. -/
theorem gap2 (a b : ℝ) : ∀ x₁ x₂, x₁ < x₂ → 0 < a →
    0 < f a b x₂ - f a b x₁ := by
  intro x₁ x₂ hlt ha
  rw [gap1 a b x₁ x₂ hlt]
  exact mul_pos ha (sub_pos.mpr hlt)

/-- Exercise 221_1, gap 3. -/
theorem gap3 (a b : ℝ) : ∀ x₁ x₂, x₁ < x₂ → a < 0 →
    f a b x₂ - f a b x₁ < 0 := by
  intro x₁ x₂ hlt ha
  rw [gap1 a b x₁ x₂ hlt]
  exact mul_neg_of_neg_of_pos ha (sub_pos.mpr hlt)

/-- Exercise 221_1, gap 4. -/
theorem gap4 (a b : ℝ) (ha : 0 < a) : StrictMono (f a b) := by
  intro x₁ x₂ hlt
  have := gap2 a b x₁ x₂ hlt ha
  linarith

/-- Exercise 221_1, gap 5. -/
theorem gap5 (a b : ℝ) (ha : a < 0) : StrictAnti (f a b) := by
  intro x₁ x₂ hlt
  have := gap3 a b x₁ x₂ hlt ha
  linarith

end ProofGap.Exercise221_1
