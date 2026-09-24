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

/-- Exercise 234, gap 1. -/
theorem gap1 : ∀ x l, IsRational l → IsRational x →
    IsRational (x + l) := by
  intro x l hl hx
  rcases hl with ⟨ql, hql⟩
  rcases hx with ⟨qx, hqx⟩
  refine ⟨qx + ql, ?_⟩
  norm_num [hqx, hql]

/-- Exercise 234, gap 2. -/
theorem gap2 : ∀ x l, IsRational l → ¬IsRational x →
    ¬IsRational (x + l) := by
  intro x l hl hx hxl
  rcases hl with ⟨ql, hql⟩
  rcases hxl with ⟨qsum, hqsum⟩
  apply hx
  refine ⟨qsum - ql, ?_⟩
  norm_num [hqsum, hql]

/-- Exercise 234, gap 3. -/
theorem gap3 : ∀ x l, IsRational l →
    chi (x + l) = indicatorValue x := by
  classical
  intro x l hl
  by_cases hx : IsRational x
  · have hsum : IsRational (x + l) := gap1 x l hl hx
    simp [chi, indicatorValue, hx, hsum]
  · have hsum : ¬IsRational (x + l) := gap2 x l hl hx
    simp [chi, indicatorValue, hx, hsum]

/-- Exercise 234, gap 4. -/
theorem gap4 : ∀ x l, IsRational l →
    indicatorValue x = chi x := by
  intro x l hl
  rfl

/-- Exercise 234, gap 5. -/
theorem gap5 : ∀ x l, IsRational l → chi (x + l) = chi x := by
  intro x l hl
  simpa [chi] using gap3 x l hl

/-- Exercise 234, gap 6. -/
theorem gap6 : ∀ l, IsRational l → Function.Periodic chi l := by
  intro l hl x
  exact gap5 x l hl

/-- Exercise 234, gap 7. -/
theorem gap7 : ∀ l, IsRational l → Function.Periodic chi l := by
  intro l hl
  exact gap6 l hl

end

end ProofGap.Exercise234
