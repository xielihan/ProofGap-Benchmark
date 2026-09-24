import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise220

noncomputable section

def f (x : ℝ) : ℝ := Real.cos x / Real.sin x
def domain : Set ℝ := Set.Ioo 0 Real.pi

/-- Source: `proof_gap/exercise_220/1.txt`. -/
theorem gap1 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    f x₂ - f x₁ =
      Real.cos x₂ / Real.sin x₂ - Real.cos x₁ / Real.sin x₁ := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  rfl

/-- Source: `proof_gap/exercise_220/2.txt`. -/
theorem gap2 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    Real.cos x₂ / Real.sin x₂ - Real.cos x₁ / Real.sin x₁ =
      (Real.cos x₂ * Real.sin x₁ - Real.cos x₁ * Real.sin x₂) /
        (Real.sin x₁ * Real.sin x₂) := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  have hs₁ : Real.sin x₁ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx₁ (lt_trans hx₁₂ hx₂))
  have hx₂pos : 0 < x₂ := lt_trans hx₁ hx₁₂
  have hs₂ : Real.sin x₂ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx₂pos hx₂)
  field_simp [hs₁, hs₂]

/-- Source: `proof_gap/exercise_220/3.txt`. -/
theorem gap3 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    (Real.cos x₂ * Real.sin x₁ - Real.cos x₁ * Real.sin x₂) /
        (Real.sin x₁ * Real.sin x₂) =
      Real.sin (x₁ - x₂) / (Real.sin x₁ * Real.sin x₂) := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  rw [Real.sin_sub]
  ring

/-- Source: `proof_gap/exercise_220/4.txt`. -/
theorem gap4 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    Real.sin (x₁ - x₂) / (Real.sin x₁ * Real.sin x₂) < 0 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  have hx₂pos : 0 < x₂ := lt_trans hx₁ hx₁₂
  have hs₁ : 0 < Real.sin x₁ :=
    Real.sin_pos_of_pos_of_lt_pi hx₁ (lt_trans hx₁₂ hx₂)
  have hs₂ : 0 < Real.sin x₂ :=
    Real.sin_pos_of_pos_of_lt_pi hx₂pos hx₂
  have hdiffpos : 0 < x₂ - x₁ := sub_pos.mpr hx₁₂
  have hdiffpi : x₂ - x₁ < Real.pi := by
    apply (sub_lt_iff_lt_add).2
    exact lt_trans hx₂ (lt_add_of_pos_right Real.pi hx₁)
  have hsin : 0 < Real.sin (x₂ - x₁) :=
    Real.sin_pos_of_pos_of_lt_pi hdiffpos hdiffpi
  have hnum : Real.sin (x₁ - x₂) < 0 := by
    rw [show x₁ - x₂ = -(x₂ - x₁) by ring, Real.sin_neg]
    exact neg_lt_zero.mpr hsin
  exact div_neg_of_neg_of_pos hnum (mul_pos hs₁ hs₂)

/-- Source: `proof_gap/exercise_220/5.txt`. -/
theorem gap5 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    f x₂ - f x₁ < 0 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  calc
    f x₂ - f x₁ =
        Real.cos x₂ / Real.sin x₂ - Real.cos x₁ / Real.sin x₁ :=
      gap1 x₁ x₂ hx₁ hx₁₂ hx₂
    _ = (Real.cos x₂ * Real.sin x₁ - Real.cos x₁ * Real.sin x₂) /
          (Real.sin x₁ * Real.sin x₂) :=
      gap2 x₁ x₂ hx₁ hx₁₂ hx₂
    _ = Real.sin (x₁ - x₂) / (Real.sin x₁ * Real.sin x₂) :=
      gap3 x₁ x₂ hx₁ hx₁₂ hx₂
    _ < 0 := gap4 x₁ x₂ hx₁ hx₁₂ hx₂

/-- Source: `proof_gap/exercise_220/6.txt`. -/
theorem gap6 : StrictAntiOn f domain := by
  intro x₁ hx₁ x₂ hx₂ hx₁₂
  change 0 < x₁ ∧ x₁ < Real.pi at hx₁
  change 0 < x₂ ∧ x₂ < Real.pi at hx₂
  exact sub_neg.mp (gap5 x₁ x₂ hx₁.1 hx₁₂ hx₂.2)

/-- Source: `proof_gap/exercise_220/7.txt`. -/
theorem gap7 : StrictAntiOn f domain := by
  exact gap6

end

end ProofGap.Exercise220
