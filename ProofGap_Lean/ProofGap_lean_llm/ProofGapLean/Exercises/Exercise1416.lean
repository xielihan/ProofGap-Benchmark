import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1416

noncomputable section

def y (x : ℝ) := (x - 1) ^ 4

private theorem sq_pos_of_ne {x : ℝ} (hx : x ≠ 0) : 0 < x ^ 2 := by
  positivity

theorem gap1 (x : ℝ) : deriv y x = 4 * (x - 1) ^ 3 := by
  have h := (hasDerivAt_id x).sub_const (1 : ℝ)
  have h2 := h.mul h
  have h3 := h2.mul h
  have h4 := h3.mul h
  have hy : HasDerivAt y (4 * (x - 1) ^ 3) x := by
    convert h4 using 1
    · funext z
      dsimp [y]
      ring
    · dsimp
      ring
  exact hy.deriv
theorem gap2 (x : ℝ) (hcrit : deriv y x = 0) : x = 1 := by
  rw [gap1] at hcrit
  have hpow : (x - 1) ^ 3 = 0 :=
    (mul_eq_zero.mp hcrit).resolve_left (by norm_num)
  have hsub : x - 1 = 0 := eq_zero_of_pow_eq_zero hpow
  exact sub_eq_zero.mp hsub
theorem gap3 (x : ℝ) (hx : x < 1) : deriv y x < 0 := by
  rw [gap1]
  have hneg : x - 1 < 0 := sub_neg.mpr hx
  have hne : x - 1 ≠ 0 := ne_of_lt hneg
  have hsq : 0 < (x - 1) ^ 2 := sq_pos_of_ne hne
  have hcube : (x - 1) ^ 3 < 0 := by
    calc
      (x - 1) ^ 3 = (x - 1) ^ 2 * (x - 1) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hsq hneg
  exact mul_neg_of_pos_of_neg (by norm_num) hcube
theorem gap4 (x : ℝ) (hx : 1 < x) : 0 < deriv y x := by
  rw [gap1]
  exact mul_pos (by norm_num) (pow_pos (sub_pos.mpr hx) 3)
theorem gap5 : IsMinOn y Set.univ 1 ∧ y 1 = 0 := by
  constructor
  · intro x _
    change y 1 ≤ y x
    calc
      y 1 = 0 := by norm_num [y]
      _ ≤ y x := by
        dsimp [y]
        positivity
  · norm_num [y]

end
end ProofGap.Exercise1416
