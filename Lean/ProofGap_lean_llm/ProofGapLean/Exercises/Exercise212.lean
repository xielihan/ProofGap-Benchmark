import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise212

def f (x : ℝ) : ℝ := x ^ 2
def domain : Set ℝ := Set.Ici 0

/-- Source: `proof_gap/exercise_212/1.txt`. -/
theorem gap1 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 ≤ x₁ →
    f x₂ - f x₁ = x₂ ^ 2 - x₁ ^ 2 := by
  intro x₁ x₂ hlt hx₁
  rfl

/-- Source: `proof_gap/exercise_212/2.txt`. -/
theorem gap2 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 ≤ x₁ →
    x₂ ^ 2 - x₁ ^ 2 = (x₂ - x₁) * (x₂ + x₁) := by
  intro x₁ x₂ hlt hx₁
  ring

/-- Source: `proof_gap/exercise_212/3.txt`. -/
theorem gap3 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 ≤ x₁ →
    0 < (x₂ - x₁) * (x₂ + x₁) := by
  intro x₁ x₂ hlt hx₁
  have hsub : 0 < x₂ - x₁ := sub_pos.mpr hlt
  have hadd : 0 < x₂ + x₁ := by linarith
  exact mul_pos hsub hadd

/-- Source: `proof_gap/exercise_212/4.txt`. -/
theorem gap4 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → 0 ≤ x₁ → 0 < f x₂ - f x₁ := by
  intro x₁ x₂ hlt hx₁
  rw [gap1 x₁ x₂ hlt hx₁, gap2 x₁ x₂ hlt hx₁]
  exact gap3 x₁ x₂ hlt hx₁

/-- Source: `proof_gap/exercise_212/5.txt`. -/
theorem gap5 : StrictMonoOn f domain := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  have := gap4 x y hxy hx
  linarith

/-- Source: `proof_gap/exercise_212/6.txt`. -/
theorem gap6 : StrictMonoOn f domain := by
  exact gap5

end ProofGap.Exercise212
