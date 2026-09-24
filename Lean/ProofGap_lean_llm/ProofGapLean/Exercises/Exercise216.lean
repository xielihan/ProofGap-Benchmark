import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise216

def f (x : ℝ) : ℝ := x ^ 2
def domain : Set ℝ := Set.Iic 0

/-- Source: `proof_gap/exercise_216/1.txt`. -/
theorem gap1 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → x₂ < 0 →
    f x₂ - f x₁ = (x₂ - x₁) * (x₂ + x₁) := by
  intro x₁ x₂ hlt hx₂
  simp only [f]
  ring

/-- Source: `proof_gap/exercise_216/2.txt`. -/
theorem gap2 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → x₂ < 0 →
    (x₂ - x₁) * (x₂ + x₁) < 0 := by
  intro x₁ x₂ hlt hx₂
  have hsub : 0 < x₂ - x₁ := sub_pos.mpr hlt
  have hadd : x₂ + x₁ < 0 := by linarith
  exact mul_neg_of_pos_of_neg hsub hadd

/-- Source: `proof_gap/exercise_216/3.txt`. -/
theorem gap3 : ∀ x₁ x₂ : ℝ, x₁ < x₂ → x₂ < 0 → f x₂ - f x₁ < 0 := by
  intro x₁ x₂ hlt hx₂
  rw [gap1 x₁ x₂ hlt hx₂]
  exact gap2 x₁ x₂ hlt hx₂

/-- Source: `proof_gap/exercise_216/4.txt`. -/
theorem gap4 : StrictAntiOn f domain := by
  intro x hx y hy hxy
  change y ≤ 0 at hy
  by_cases hy0 : y = 0
  · subst y
    simp only [f]
    nlinarith [sq_pos_of_neg hxy]
  · have hyneg : y < 0 := lt_of_le_of_ne hy hy0
    have := gap3 x y hxy hyneg
    linarith

/-- Source: `proof_gap/exercise_216/5.txt`. -/
theorem gap5 : StrictAntiOn f domain := by
  exact gap4

end ProofGap.Exercise216
