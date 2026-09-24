import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Interval

namespace ProofGap.Exercise2472

noncomputable section

def profile (a b x : ℝ) : ℝ := b * (x / a) ^ (2 / 3 : ℝ)

def volume (a b : ℝ) : ℝ :=
  Real.pi * b ^ 2 * ∫ x in 0..a, (x / a) ^ (4 / 3 : ℝ)

theorem gap1 (a b V : ℝ) (hV : V = volume a b) :
    V = Real.pi * b ^ 2 *
      ∫ x in 0..a, (x / a) ^ (4 / 3 : ℝ) := by
  simpa [volume] using hV

theorem gap2 (a b V : ℝ) (ha : 0 < a) (hV : V = volume a b) :
    V = 3 / 7 * Real.pi * a * b ^ 2 := by
  have ha0 : 0 ≤ a := ha.le
  have hpow_pos : 0 < a ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos ha _
  have hpow_ne : a ^ (4 / 3 : ℝ) ≠ 0 := ne_of_gt hpow_pos
  have hpow : a ^ (7 / 3 : ℝ) = a ^ (4 / 3 : ℝ) * a := by
    calc
      a ^ (7 / 3 : ℝ) = a ^ ((4 / 3 : ℝ) + 1) := by norm_num
      _ = a ^ (4 / 3 : ℝ) * a ^ (1 : ℝ) := by
        rw [Real.rpow_add ha]
      _ = a ^ (4 / 3 : ℝ) * a := by rw [Real.rpow_one]
  have hpowint :
      (∫ x in (0 : ℝ)..a, x ^ (4 / 3 : ℝ)) =
        (3 / 7 : ℝ) * a ^ (7 / 3 : ℝ) := by
    norm_num [integral_rpow, ha0] <;> ring
  have hI :
      (∫ x in (0 : ℝ)..a, (x / a) ^ (4 / 3 : ℝ)) =
        (3 / 7 : ℝ) * a := by
    calc
      (∫ x in (0 : ℝ)..a, (x / a) ^ (4 / 3 : ℝ)) =
          ∫ x in (0 : ℝ)..a,
            (a ^ (4 / 3 : ℝ))⁻¹ * x ^ (4 / 3 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx0 : 0 ≤ x := by
          simp only [Set.uIcc_of_le ha0, Set.mem_Icc] at hx
          exact hx.1
        change (x / a) ^ (4 / 3 : ℝ) =
          (a ^ (4 / 3 : ℝ))⁻¹ * x ^ (4 / 3 : ℝ)
        rw [Real.div_rpow hx0 ha0]
        simp [div_eq_mul_inv, mul_comm]
      _ = (a ^ (4 / 3 : ℝ))⁻¹ *
          (∫ x in (0 : ℝ)..a, x ^ (4 / 3 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = (a ^ (4 / 3 : ℝ))⁻¹ *
          ((3 / 7 : ℝ) * a ^ (7 / 3 : ℝ)) := by rw [hpowint]
      _ = (3 / 7 : ℝ) * a := by
        rw [hpow]
        field_simp [hpow_ne]
        <;> ring
  rw [hV]
  simp only [volume]
  rw [hI]
  ring

end

end ProofGap.Exercise2472
