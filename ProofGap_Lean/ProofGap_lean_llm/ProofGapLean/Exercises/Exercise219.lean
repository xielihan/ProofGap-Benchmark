import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise219

noncomputable section

def f (x : ℝ) : ℝ := Real.cos x / Real.sin x
def domain : Set ℝ := Set.Ioo 0 Real.pi

/-- Exercise 219, gap 1. -/
theorem gap1 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    f x₂ - f x₁ =
      Real.cos x₂ / Real.sin x₂ - Real.cos x₁ / Real.sin x₁ := by
  intro x₁ x₂ _ _ _
  rfl

/-- Exercise 219, gap 2. -/
theorem gap2 : ∀ x₁ x₂ : ℝ,
    Real.cos x₂ / Real.sin x₂ - Real.cos x₁ / Real.sin x₁ =
      f x₂ - f x₁ := by
  intro x₁ x₂
  rfl

/-- Exercise 219, gap 3; denominators must be nonzero. -/
theorem gap3 : ∀ x₁ x₂ : ℝ, Real.sin x₁ ≠ 0 → Real.sin x₂ ≠ 0 →
    Real.cos x₂ / Real.sin x₂ - Real.cos x₁ / Real.sin x₁ =
      (Real.cos x₂ * Real.sin x₁ - Real.sin x₂ * Real.cos x₁) /
        (Real.sin x₁ * Real.sin x₂) := by
  intro x₁ x₂ h₁ h₂
  field_simp [h₁, h₂] <;> ring

/-- Exercise 219, gap 4; denominators must be nonzero. -/
theorem gap4 : ∀ x₁ x₂ : ℝ, Real.sin x₁ ≠ 0 → Real.sin x₂ ≠ 0 →
    (Real.cos x₂ * Real.sin x₁ - Real.sin x₂ * Real.cos x₁) /
        (Real.sin x₁ * Real.sin x₂) =
      -Real.sin (x₂ - x₁) / (Real.sin x₁ * Real.sin x₂) := by
  intro x₁ x₂ _ _
  rw [Real.sin_sub]
  ring

/-- Exercise 219, gap 5; denominators must be nonzero. -/
theorem gap5 : ∀ x₁ x₂ : ℝ, Real.sin x₁ ≠ 0 → Real.sin x₂ ≠ 0 →
    f x₂ - f x₁ = -Real.sin (x₂ - x₁) / (Real.sin x₁ * Real.sin x₂) := by
  intro x₁ x₂ h₁ h₂
  calc
    f x₂ - f x₁ = Real.cos x₂ / Real.sin x₂ - Real.cos x₁ / Real.sin x₁ := by rfl
    _ = (Real.cos x₂ * Real.sin x₁ - Real.sin x₂ * Real.cos x₁) /
          (Real.sin x₁ * Real.sin x₂) := gap3 x₁ x₂ h₁ h₂
    _ = -Real.sin (x₂ - x₁) / (Real.sin x₁ * Real.sin x₂) :=
      gap4 x₁ x₂ h₁ h₂

/-- Exercise 219, gap 6. -/
theorem gap6 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    0 < Real.sin x₁ := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  exact Real.sin_pos_of_pos_of_lt_pi hx₁ (lt_trans hx₁₂ hx₂)

/-- Exercise 219, gap 7. -/
theorem gap7 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    0 < Real.sin x₂ := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  exact Real.sin_pos_of_pos_of_lt_pi (lt_trans hx₁ hx₁₂) hx₂

/-- Exercise 219, gap 8. -/
theorem gap8 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    0 < Real.sin (x₂ - x₁) := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  exact Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hx₁₂)
    (lt_trans (sub_lt_self x₂ hx₁) hx₂)

/-- Exercise 219, gap 9. -/
theorem gap9 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    -Real.sin (x₂ - x₁) / (Real.sin x₁ * Real.sin x₂) < 0 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  have hs₁ : 0 < Real.sin x₁ := gap6 x₁ x₂ hx₁ hx₁₂ hx₂
  have hs₂ : 0 < Real.sin x₂ := gap7 x₁ x₂ hx₁ hx₁₂ hx₂
  have hsd : 0 < Real.sin (x₂ - x₁) := gap8 x₁ x₂ hx₁ hx₁₂ hx₂
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hsd) (mul_pos hs₁ hs₂)

/-- Exercise 219, gap 10. -/
theorem gap10 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    f x₂ - f x₁ < 0 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  have hs₁ : 0 < Real.sin x₁ := gap6 x₁ x₂ hx₁ hx₁₂ hx₂
  have hs₂ : 0 < Real.sin x₂ := gap7 x₁ x₂ hx₁ hx₁₂ hx₂
  calc
    f x₂ - f x₁ = -Real.sin (x₂ - x₁) / (Real.sin x₁ * Real.sin x₂) :=
      gap5 x₁ x₂ (ne_of_gt hs₁) (ne_of_gt hs₂)
    _ < 0 := gap9 x₁ x₂ hx₁ hx₁₂ hx₂

/-- Exercise 219, gap 11. -/
theorem gap11 : StrictAntiOn f domain := by
  intro x₁ hx₁ x₂ hx₂ hx₁₂
  exact sub_neg.mp (gap10 x₁ x₂ hx₁.1 hx₁₂ hx₂.2)

/-- Exercise 219, gap 12. -/
theorem gap12 : StrictAntiOn f domain := by
  exact gap11

end

end ProofGap.Exercise219
