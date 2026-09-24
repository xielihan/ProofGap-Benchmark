import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise215

noncomputable section

def f (x : ℝ) : ℝ := Real.tan x
def domain : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)

/-- Source: `proof_gap/exercise_215/1.txt`. -/
theorem gap1 : ∀ x₁ x₂, f x₂ - f x₁ = Real.tan x₂ - Real.tan x₁ := by
  intro x₁ x₂
  rfl

/-- Source: `proof_gap/exercise_215/2.txt`. -/
theorem gap2 : ∀ x₁ x₂ : ℝ,
    Real.tan x₂ - Real.tan x₁ =
      Real.sin x₂ / Real.cos x₂ - Real.sin x₁ / Real.cos x₁ := by
  intro x₁ x₂
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]

/-- Source: `proof_gap/exercise_215/3.txt`; denominators must be nonzero. -/
theorem gap3 : ∀ x₁ x₂ : ℝ, Real.cos x₁ ≠ 0 → Real.cos x₂ ≠ 0 →
    Real.sin x₂ / Real.cos x₂ - Real.sin x₁ / Real.cos x₁ =
      (Real.sin x₂ * Real.cos x₁ - Real.cos x₂ * Real.sin x₁) /
        (Real.cos x₁ * Real.cos x₂) := by
  intro x₁ x₂ h₁ h₂
  field_simp [h₁, h₂]
  <;> ring

/-- Source: `proof_gap/exercise_215/4.txt`; denominators must be nonzero. -/
theorem gap4 : ∀ x₁ x₂ : ℝ, Real.cos x₁ ≠ 0 → Real.cos x₂ ≠ 0 →
    (Real.sin x₂ * Real.cos x₁ - Real.cos x₂ * Real.sin x₁) /
        (Real.cos x₁ * Real.cos x₂) =
      Real.sin (x₂ - x₁) / (Real.cos x₁ * Real.cos x₂) := by
  intro x₁ x₂ _ _
  rw [Real.sin_sub]

/-- Source: `proof_gap/exercise_215/5.txt`; denominators must be nonzero. -/
theorem gap5 : ∀ x₁ x₂ : ℝ, Real.cos x₁ ≠ 0 → Real.cos x₂ ≠ 0 →
    f x₂ - f x₁ = Real.sin (x₂ - x₁) / (Real.cos x₁ * Real.cos x₂) := by
  intro x₁ x₂ h₁ h₂
  calc
    f x₂ - f x₁ = Real.tan x₂ - Real.tan x₁ := gap1 x₁ x₂
    _ = Real.sin x₂ / Real.cos x₂ - Real.sin x₁ / Real.cos x₁ := gap2 x₁ x₂
    _ = (Real.sin x₂ * Real.cos x₁ - Real.cos x₂ * Real.sin x₁) /
          (Real.cos x₁ * Real.cos x₂) := gap3 x₁ x₂ h₁ h₂
    _ = Real.sin (x₂ - x₁) / (Real.cos x₁ * Real.cos x₂) := gap4 x₁ x₂ h₁ h₂

/-- Source: `proof_gap/exercise_215/6.txt`. -/
theorem gap6 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < Real.cos x₁ := by
  intro x₁ x₂ hleft hlt hright
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

/-- Source: `proof_gap/exercise_215/7.txt`. -/
theorem gap7 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < Real.cos x₂ := by
  intro x₁ x₂ hleft hlt hright
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

/-- Source: `proof_gap/exercise_215/8.txt`. -/
theorem gap8 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < Real.sin (x₂ - x₁) := by
  intro x₁ x₂ hleft hlt hright
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · linarith

/-- Source: `proof_gap/exercise_215/9.txt`. -/
theorem gap9 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < f x₂ - f x₁ := by
  intro x₁ x₂ hleft hlt hright
  have hc₁ : 0 < Real.cos x₁ := gap6 x₁ x₂ hleft hlt hright
  have hc₂ : 0 < Real.cos x₂ := gap7 x₁ x₂ hleft hlt hright
  have hs : 0 < Real.sin (x₂ - x₁) := gap8 x₁ x₂ hleft hlt hright
  rw [gap5 x₁ x₂ (ne_of_gt hc₁) (ne_of_gt hc₂)]
  exact div_pos hs (mul_pos hc₁ hc₂)

/-- Source: `proof_gap/exercise_215/10.txt`. -/
theorem gap10 : StrictMonoOn f domain := by
  intro x₁ hx₁ x₂ hx₂ hlt
  exact sub_pos.mp (gap9 x₁ x₂ hx₁.1 hlt hx₂.2)

/-- Source: `proof_gap/exercise_215/11.txt`. -/
theorem gap11 : StrictMonoOn f domain := by
  exact gap10

end

end ProofGap.Exercise215
