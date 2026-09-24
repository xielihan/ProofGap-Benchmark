import ProofGapLean.Prelude.Core
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise234

noncomputable section

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

noncomputable def indicatorValue (x : ℝ) : ℝ := by
  classical
  exact if IsRational x then 1 else 0

def chi (x : ℝ) : ℝ := indicatorValue x

/-- Source: `proof_gap/exercise_234/1.txt`. -/
theorem gap1 : ∀ x l, IsRational l → IsRational x →
    IsRational (x + l) := by
  intro x l hl hx
  rcases hl with ⟨ql, hql⟩
  rcases hx with ⟨qx, hqx⟩
  refine ⟨qx + ql, ?_⟩
  norm_num [hqx, hql]

/-- Source: `proof_gap/exercise_234/2.txt`. -/
theorem gap2 : ∀ x l, IsRational l → ¬IsRational x →
    ¬IsRational (x + l) := by
  intro x l hl hx hxl
  rcases hl with ⟨ql, hql⟩
  rcases hxl with ⟨qsum, hqsum⟩
  apply hx
  refine ⟨qsum - ql, ?_⟩
  norm_num [hqsum, hql]

/-- Source: `proof_gap/exercise_234/3.txt`. -/
theorem gap3 : ∀ x l, IsRational l →
    chi (x + l) = indicatorValue x := by
  classical
  intro x l hl
  by_cases hx : IsRational x
  · have hsum : IsRational (x + l) := gap1 x l hl hx
    simp [chi, indicatorValue, hx, hsum]
  · have hsum : ¬IsRational (x + l) := gap2 x l hl hx
    simp [chi, indicatorValue, hx, hsum]

/-- Source: `proof_gap/exercise_234/4.txt`. -/
theorem gap4 : ∀ x l, IsRational l →
    indicatorValue x = chi x := by
  intro x l hl
  rfl

/-- Source: `proof_gap/exercise_234/5.txt`. -/
theorem gap5 : ∀ x l, IsRational l → chi (x + l) = chi x := by
  intro x l hl
  simpa [chi] using gap3 x l hl

/-- Source: `proof_gap/exercise_234/6.txt`. -/
theorem gap6 : ∀ l, IsRational l → Function.Periodic chi l := by
  intro l hl x
  exact gap5 x l hl

/-- Source: `proof_gap/exercise_234/7.txt`. -/
theorem gap7 : ∀ l, IsRational l → Function.Periodic chi l := by
  intro l hl
  exact gap6 l hl

end

end ProofGap.Exercise234
