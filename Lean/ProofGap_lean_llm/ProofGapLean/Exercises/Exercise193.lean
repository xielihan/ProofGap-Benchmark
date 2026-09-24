import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise193

noncomputable section

def f (x : ℝ) : ℝ := (1 - x) / (1 + x)

/-- Exercise 193, gap 1. -/
theorem gap1 : f 0 = 1 := by
  norm_num [f]

/-- Exercise 193, gap 2; exclude x=1. -/
theorem gap2 : ∀ x : ℝ, x ≠ 1 → f (-x) = (1 + x) / (1 - x) := by
  intro x _
  simp only [f]
  congr 1 <;> ring

/-- Exercise 193, gap 3; exclude x=-2. -/
theorem gap3 : ∀ x : ℝ, x ≠ -2 →
    f (x + 1) = (1 - (x + 1)) / (1 + x + 1) := by
  intro x _
  simp only [f]
  congr 1
  ring

/-- Exercise 193, gap 4; exclude x=-2. -/
theorem gap4 : ∀ x : ℝ, x ≠ -2 →
    (1 - (x + 1)) / (1 + x + 1) = -x / (x + 2) := by
  intro x _
  congr 1 <;> ring

/-- Exercise 193, gap 5; exclude x=-2. -/
theorem gap5 : ∀ x : ℝ, x ≠ -2 → f (x + 1) = -x / (x + 2) := by
  intro x hx
  rw [gap3 x hx, gap4 x hx]

/-- Exercise 193, gap 6; exclude the pole x=-1. -/
theorem gap6 : ∀ x : ℝ, x ≠ -1 → f x + 1 = (1 - x) / (1 + x) + 1 := by
  intro x _
  rfl

/-- Exercise 193, gap 7; exclude the pole x=-1. -/
theorem gap7 : ∀ x : ℝ, x ≠ -1 →
    (1 - x) / (1 + x) + 1 = 2 / (1 + x) := by
  intro x hx
  have h : 1 + x ≠ 0 := by
    intro hzero
    apply hx
    linarith
  field_simp [h]
  ring

/-- Exercise 193, gap 8; exclude the pole x=-1. -/
theorem gap8 : ∀ x : ℝ, x ≠ -1 → f x + 1 = 2 / (1 + x) := by
  intro x hx
  rw [gap6 x hx, gap7 x hx]

/-- Exercise 193, gap 9; exclude x=0 and the induced pole x=-1. -/
theorem gap9 : ∀ x : ℝ, x ≠ 0 → x ≠ -1 →
    f (1 / x) = (1 - 1 / x) / (1 + 1 / x) := by
  intro x _ _
  rfl

/-- Exercise 193, gap 10. -/
theorem gap10 : ∀ x : ℝ, x ≠ 0 → x ≠ -1 →
    (1 - 1 / x) / (1 + 1 / x) = (x - 1) / (x + 1) := by
  intro x hx hxm
  have hxp : x + 1 ≠ 0 := by
    intro hzero
    apply hxm
    linarith
  field_simp [hx, hxp]

/-- Exercise 193, gap 11. -/
theorem gap11 : ∀ x : ℝ, x ≠ 0 → x ≠ -1 →
    f (1 / x) = (x - 1) / (x + 1) := by
  intro x hx hxm
  rw [gap9 x hx hxm, gap10 x hx hxm]

/-- Exercise 193, gap 12; exclude both poles and the zero of f. -/
theorem gap12 : ∀ x : ℝ, x ≠ -1 → x ≠ 1 →
    1 / f x = 1 / ((1 - x) / (1 + x)) := by
  intro x _ _
  rfl

/-- Exercise 193, gap 13. -/
theorem gap13 : ∀ x : ℝ, x ≠ -1 → x ≠ 1 →
    1 / ((1 - x) / (1 + x)) = (1 + x) / (1 - x) := by
  intro x hxm hxp
  have hden : 1 - x ≠ 0 := by
    intro hzero
    apply hxp
    linarith
  have hnum : 1 + x ≠ 0 := by
    intro hzero
    apply hxm
    linarith
  field_simp [hden, hnum]

/-- Exercise 193, gap 14. -/
theorem gap14 : ∀ x : ℝ, x ≠ -1 → x ≠ 1 →
    1 / f x = (1 + x) / (1 - x) := by
  intro x hxm hxp
  rw [gap12 x hxm hxp, gap13 x hxm hxp]

end

end ProofGap.Exercise193
