import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise226

noncomputable section

def y (x : ℝ) : ℝ := (1 - x) / (1 + x)

/-- Exercise 226, gap 1; exclude x=-1. -/
theorem gap1 : ∀ x : ℝ, x ≠ -1 → y x + x * y x = 1 - x := by
  intro x hx
  have hden : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  simp only [y]
  field_simp [hden]

/-- Exercise 226, gap 2; the map is an involution off its pole. -/
theorem gap2 : ∀ x : ℝ, x ≠ -1 → x = (1 - y x) / (1 + y x) := by
  intro x hx
  have hden : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  have hyformula : 1 + y x = 2 / (1 + x) := by
    simp only [y]
    field_simp [hden]
    ring
  have hyden : 1 + y x ≠ 0 := by
    rw [hyformula]
    exact div_ne_zero (by norm_num) hden
  rw [eq_div_iff hyden]
  simp only [y]
  field_simp [hden]
  ring

end

end ProofGap.Exercise226
