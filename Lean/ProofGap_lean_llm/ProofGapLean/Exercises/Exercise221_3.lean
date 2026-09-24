import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise221_3

def f (x : ℝ) : ℝ := x ^ 3

/-- Source: `proof_gap/exercise_221_3/1.txt`. -/
theorem gap1 : ∀ x₁ x₂, x₁ < x₂ → f x₂ - f x₁ = x₂ ^ 3 - x₁ ^ 3 := by
  intro x₁ x₂ h
  rfl

/-- Source: `proof_gap/exercise_221_3/2.txt`. -/
theorem gap2 : ∀ x₁ x₂ : ℝ, x₁ < x₂ →
    x₂ ^ 3 - x₁ ^ 3 = (x₂ - x₁) * (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2) := by
  intro x₁ x₂ h
  ring

/-- Source: `proof_gap/exercise_221_3/3.txt`. -/
theorem gap3 : ∀ x₁ x₂ : ℝ, x₁ < x₂ →
    0 < (x₂ - x₁) * (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2) := by
  intro x₁ x₂ h
  have hdiff : 0 < x₂ - x₁ := sub_pos.mpr h
  have hdiff_mul : 0 < (x₂ - x₁) * (x₂ - x₁) := mul_pos hdiff hdiff
  have hquad : 0 < x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 := by
    nlinarith [hdiff_mul, sq_nonneg (x₂ + x₁)]
  exact mul_pos hdiff hquad

/-- Source: `proof_gap/exercise_221_3/4.txt`. -/
theorem gap4 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 < f x₂ - f x₁ := by
  intro x₁ x₂ h
  rw [gap1 x₁ x₂ h, gap2 x₁ x₂ h]
  exact gap3 x₁ x₂ h

/-- Source: `proof_gap/exercise_221_3/5.txt`. -/
theorem gap5 : StrictMono f := by
  intro x₁ x₂ h
  exact sub_pos.mp (gap4 x₁ x₂ h)

/-- Source: `proof_gap/exercise_221_3/6.txt`. -/
theorem gap6 : StrictMono f := by
  exact gap5

end ProofGap.Exercise221_3
