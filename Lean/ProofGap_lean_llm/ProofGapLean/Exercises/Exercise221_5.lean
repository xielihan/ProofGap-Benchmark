import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise221_5

noncomputable section

def f (a x : ℝ) : ℝ := Real.rpow a x

/-- Source: `proof_gap/exercise_221_5/1.txt`. -/
theorem gap1 (a : ℝ) (ha : 0 < a) : ∀ x₁ x₂, x₁ < x₂ →
    f a x₂ - f a x₁ = Real.rpow a x₂ - Real.rpow a x₁ := by
  intro x₁ x₂ hx
  rfl

/-- Source: `proof_gap/exercise_221_5/2.txt`. -/
theorem gap2 (a : ℝ) : ∀ x₁ x₂, x₁ < x₂ → 0 < a → a < 1 →
    f a x₂ - f a x₁ < 0 := by
  intro x₁ x₂ hx ha0 ha1
  apply sub_neg.mpr
  change Real.rpow a x₂ < Real.rpow a x₁
  exact (Real.strictAnti_rpow_of_base_lt_one ha0 ha1) hx

/-- Source: `proof_gap/exercise_221_5/3.txt`. -/
theorem gap3 (a : ℝ) : ∀ x₁ x₂, x₁ < x₂ → 1 < a →
    0 < f a x₂ - f a x₁ := by
  intro x₁ x₂ hx ha
  apply sub_pos.mpr
  change Real.rpow a x₁ < Real.rpow a x₂
  exact (Real.strictMono_rpow_of_base_gt_one ha) hx

/-- Source: `proof_gap/exercise_221_5/4.txt`. -/
theorem gap4 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : StrictAnti (f a) := by
  intro x₁ x₂ hx
  exact sub_neg.mp (gap2 a x₁ x₂ hx ha0 ha1)

/-- Source: `proof_gap/exercise_221_5/5.txt`. -/
theorem gap5 (a : ℝ) (ha : 1 < a) : StrictMono (f a) := by
  intro x₁ x₂ hx
  exact sub_pos.mp (gap3 a x₁ x₂ hx ha)

end

end ProofGap.Exercise221_5
