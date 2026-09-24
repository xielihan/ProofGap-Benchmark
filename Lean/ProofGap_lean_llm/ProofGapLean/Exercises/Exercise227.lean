import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise227

noncomputable section

def y (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

/-- Source: `proof_gap/exercise_227/1.txt`. -/
theorem gap1 : ∀ x : ℝ, -1 ≤ x → x ≤ 0 →
    x = -Real.sqrt (1 - (y x) ^ 2) := by
  intro x hxlo hxhi
  have hrad : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hy : (y x) ^ 2 = 1 - x ^ 2 := by
    simp [y, Real.sq_sqrt hrad]
  rw [hy]
  ring_nf
  rw [Real.sqrt_sq_eq_abs, abs_of_nonpos hxhi]
  ring

/-- Source: `proof_gap/exercise_227/2.txt`. -/
theorem gap2 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    x = Real.sqrt (1 - (y x) ^ 2) := by
  intro x hxlo hxhi
  have hrad : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hy : (y x) ^ 2 = 1 - x ^ 2 := by
    simp [y, Real.sq_sqrt hrad]
  rw [hy]
  ring_nf
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hxlo]

end

end ProofGap.Exercise227
