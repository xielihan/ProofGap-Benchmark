import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1023

theorem gap1 (x : ℝ) (hx : x < 0) :
    2 * x ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg (x - 1)]

theorem gap2 :
    ¬ ∀ x : ℝ, x < 0 → (2 : ℝ) ≤ 2 * x := by
  intro h
  have hneg := h (-1) (by norm_num)
  norm_num at hneg

theorem gap3 :
    ¬ ∀ x : ℝ, x < 0 → (2 : ℝ) ≤ 2 * x := by
  exact gap2

theorem gap4 :
    ¬ ∀ x : ℝ, x < 0 → (2 : ℝ) ≤ 2 * x := by
  exact gap2

end ProofGap.Exercise1023
