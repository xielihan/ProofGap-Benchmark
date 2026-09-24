import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise212

def f (x : ℝ) : ℝ := x ^ 2
def domain : Set ℝ := Set.Ici 0

/-- Exercise 212, gap 1. -/
theorem gap1 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 ≤ x₁ →
    f x₂ - f x₁ = x₂ ^ 2 - x₁ ^ 2 := by
  intro x₁ x₂ hlt hx₁
  rfl

/-- Exercise 212, gap 2. -/
theorem gap2 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 ≤ x₁ →
    x₂ ^ 2 - x₁ ^ 2 = (x₂ - x₁) * (x₂ + x₁) := by
  intro x₁ x₂ hlt hx₁
  ring

/-- Exercise 212, gap 3. -/
theorem gap3 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 ≤ x₁ →
    0 < (x₂ - x₁) * (x₂ + x₁) := by
  intro x₁ x₂ hlt hx₁
  have hsub : 0 < x₂ - x₁ := sub_pos.mpr hlt
  have hadd : 0 < x₂ + x₁ := by linarith
  exact mul_pos hsub hadd

/-- Exercise 212, gap 4. -/
theorem gap4 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 ≤ x₁ → 0 < f x₂ - f x₁ := by
  intro x₁ x₂ hlt hx₁
  rw [gap1 x₁ x₂ hlt hx₁, gap2 x₁ x₂ hlt hx₁]
  exact gap3 x₁ x₂ hlt hx₁

/-- Exercise 212, gap 5. -/
theorem gap5 : StrictMonoOn f domain := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  have := gap4 x y hxy hx
  linarith

/-- Exercise 212, gap 6. -/
theorem gap6 : StrictMonoOn f domain := by
  exact gap5

end ProofGap.Exercise212
