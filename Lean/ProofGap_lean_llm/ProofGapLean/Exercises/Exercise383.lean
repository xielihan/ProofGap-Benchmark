import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise383

noncomputable section

def f (x : ℝ) : ℝ := (1 + x ^ 2) / (1 + x ^ 4)

def BoundedOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ s, |g x| ≤ M

/-- Source: `proof_gap/exercise_383/1.txt`. -/
theorem gap1 : ∀ x, |x| ≤ 1 → |f x| < (1 + 1 : ℝ) / 1 := by
  intro x hx
  rw [abs_of_nonneg]
  · unfold f
    have hden : 0 < 1 + x ^ 4 := by
      nlinarith [sq_nonneg (x ^ 2)]
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_nonneg x, sq_nonneg (2 * x ^ 2 - 1)]
  · unfold f
    exact div_nonneg (by nlinarith [sq_nonneg x])
      (by nlinarith [sq_nonneg (x ^ 2)])

/-- Source: `proof_gap/exercise_383/2.txt`. -/
theorem gap2 : ∀ x : ℝ, |x| ≤ 1 → (1 + 1 : ℝ) / 1 = 2 := by
  intro x hx
  norm_num

/-- Source: `proof_gap/exercise_383/3.txt`. -/
theorem gap3 : ∀ x, |x| ≤ 1 → |f x| < 2 := by
  intro x hx
  calc
    |f x| < (1 + 1 : ℝ) / 1 := gap1 x hx
    _ = 2 := gap2 x hx

/-- Source: `proof_gap/exercise_383/4.txt`. -/
theorem gap4 : ∀ x, 1 < |x| →
    |f x| < (1 + x ^ 4) / (1 + x ^ 4) := by
  intro x hx
  have hx2 : 1 < x ^ 2 := by
    by_cases hnonneg : 0 ≤ x
    · rw [abs_of_nonneg hnonneg] at hx
      have hprod : 0 < (x - 1) * (x + 1) :=
        mul_pos (sub_pos.mpr hx) (by nlinarith)
      nlinarith [hprod]
    · have hnonpos : x ≤ 0 := le_of_not_ge hnonneg
      rw [abs_of_nonpos hnonpos] at hx
      have hprod : 0 < (-x - 1) * (-x + 1) :=
        mul_pos (by nlinarith) (by nlinarith)
      nlinarith [hprod]
  have hden : 0 < 1 + x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2)]
  rw [abs_of_nonneg]
  · rw [div_self (ne_of_gt hden)]
    unfold f
    apply (div_lt_iff₀ hden).2
    have hprod : 0 < (x ^ 2 - 1) * x ^ 2 :=
      mul_pos (sub_pos.mpr hx2) (by nlinarith)
    nlinarith [hprod]
  · unfold f
    exact div_nonneg (by nlinarith [sq_nonneg x]) hden.le

/-- Source: `proof_gap/exercise_383/5.txt`. -/
theorem gap5 : ∀ x : ℝ, 1 < |x| →
    (1 + x ^ 4) / (1 + x ^ 4) = 1 := by
  intro x hx
  exact div_self (ne_of_gt (by nlinarith [sq_nonneg (x ^ 2)]))

/-- Source: `proof_gap/exercise_383/6.txt`. -/
theorem gap6 : ∀ x, 1 < |x| → |f x| < 1 := by
  intro x hx
  calc
    |f x| < (1 + x ^ 4) / (1 + x ^ 4) := gap4 x hx
    _ = 1 := gap5 x hx

/-- Source: `proof_gap/exercise_383/7.txt`. -/
theorem gap7 : ∀ x : ℝ, |f x| < 2 := by
  intro x
  by_cases hx : |x| ≤ 1
  · exact gap3 x hx
  · have hx' : 1 < |x| := lt_of_not_ge hx
    exact lt_trans (gap6 x hx') (by norm_num)

/-- Source: `proof_gap/exercise_383/8.txt`. -/
theorem gap8 : BoundedOn f Set.univ := by
  refine ⟨2, ?_⟩
  intro x hx
  exact (gap7 x).le

/-- Source: `proof_gap/exercise_383/9.txt`. -/
theorem gap9 : BoundedOn f Set.univ := by
  exact gap8

end

end ProofGap.Exercise383
