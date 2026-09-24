import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1086

noncomputable section

def y (a x : ℝ) : ℝ := (1 / a) * Real.arctan (x / a)
def differentialAt (a x dx : ℝ) : ℝ := deriv (y a) x * dx

theorem gap1 (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (y a)
      ((1 / a) * (1 / a) * (1 / (1 + x ^ 2 / a ^ 2))) x := by
  unfold y
  simpa only [div_pow, mul_assoc, mul_left_comm, mul_comm] using
    (((Real.hasDerivAt_arctan (x / a)).comp x
      ((hasDerivAt_id x).div_const a)).const_mul (1 / a))

theorem gap2 (a x : ℝ) (ha : a ≠ 0) :
    (1 / a) * (1 / a) * (1 / (1 + x ^ 2 / a ^ 2)) =
      1 / (a ^ 2 + x ^ 2) := by
  have ha_sq_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have ha_sq_pos : 0 < a ^ 2 :=
    lt_of_le_of_ne (sq_nonneg a) (Ne.symm ha_sq_ne)
  have hx_div_nonneg : 0 ≤ x ^ 2 / a ^ 2 :=
    div_nonneg (sq_nonneg x) (le_of_lt ha_sq_pos)
  have hden : 1 + x ^ 2 / a ^ 2 ≠ 0 := by
    nlinarith
  have hsum : a ^ 2 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  field_simp [ha, ha_sq_ne, hden, hsum] <;> ring

theorem gap3 (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (y a) (1 / (a ^ 2 + x ^ 2)) x := by
  rw [← gap2 a x ha]
  exact gap1 a x ha

theorem gap4 (a x dx : ℝ) (ha : a ≠ 0) :
    differentialAt a x dx = dx / (a ^ 2 + x ^ 2) := by
  unfold differentialAt
  rw [(gap3 a x ha).deriv]
  ring

end

end ProofGap.Exercise1086
