import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open scoped Interval

namespace ProofGap.Exercise2509

noncomputable section

def quarterArea (a b : ℝ) : ℝ := Real.pi * a * b / 4
def solidVolume (a b : ℝ) : ℝ :=
  Real.pi * ∫ x in -a..a, (b ^ 2 / a ^ 2) * (a ^ 2 - x ^ 2)

theorem gap1 (a b S : ℝ) (hS : S = quarterArea a b) :
    S = Real.pi * a * b / 4 := by
  simpa [quarterArea] using hS

theorem gap2 (a b x y : ℝ) (ha : a ≠ 0)
    (hEllipse : x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1)
    (hb : b ≠ 0) :
    y ^ 2 = (b ^ 2 / a ^ 2) * (a ^ 2 - x ^ 2) := by
  field_simp [ha, hb] at hEllipse ⊢
  nlinarith [hEllipse]

theorem gap3 (a b V : ℝ) (hV : V = solidVolume a b) :
    V = Real.pi *
      ∫ x in -a..a, (b ^ 2 / a ^ 2) * (a ^ 2 - x ^ 2) := by
  simpa [solidVolume] using hV

theorem gap4 (a b : ℝ) (ha : 0 < a) :
    Real.pi *
      (∫ x in -a..a, (b ^ 2 / a ^ 2) * (a ^ 2 - x ^ 2)) =
        4 / 3 * Real.pi * a * b ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hconst :
      IntervalIntegrable
        (fun _ : ℝ => (b ^ 2 / a ^ 2) * a ^ 2)
        MeasureTheory.volume (-a) a :=
    continuous_const.intervalIntegrable (-a) a
  have hpow :
      IntervalIntegrable
        (fun x : ℝ => (b ^ 2 / a ^ 2) * x ^ 2)
        MeasureTheory.volume (-a) a :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable (-a) a
  have hx2 :
      (∫ x : ℝ in -a..a, x ^ 2) =
        a ^ 3 / 3 - (-a) ^ 3 / 3 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => x ^ 3 / 3)
      (f' := fun x : ℝ => x ^ 2) ?_ ?_
    · intro x _
      have hcube :
          HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
        convert (hasDerivAt_id x).pow 3 using 1 <;> norm_num <;> ring
      convert hcube.div_const 3 using 1 <;> norm_num <;> ring
    · exact (continuous_id.pow 2).intervalIntegrable (-a) a
  simp only [mul_sub]
  rw [intervalIntegral.integral_sub hconst hpow]
  rw [intervalIntegral.integral_const]
  rw [intervalIntegral.integral_const_mul]
  rw [hx2]
  simp only [smul_eq_mul]
  field_simp [ha0] <;> ring

theorem gap5 (a b V : ℝ) (ha : 0 < a)
    (hV : V = solidVolume a b) :
    V = 4 / 3 * Real.pi * a * b ^ 2 := by
  calc
    V = solidVolume a b := hV
    _ = 4 / 3 * Real.pi * a * b ^ 2 := by
      simpa [solidVolume] using gap4 a b ha

theorem gap6 (a b η : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hη : η = 4 * b / (3 * Real.pi)) :
    2 * Real.pi * η * (Real.pi * a * b / 4) =
      2 / 3 * Real.pi * a * b ^ 2 := by
  rw [hη]
  field_simp [Real.pi_ne_zero]

theorem gap7 (a b η : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hPappus :
      2 * Real.pi * η * quarterArea a b =
        2 / 3 * Real.pi * a * b ^ 2) :
    η = 4 * b / (3 * Real.pi) := by
  have hP := hPappus
  rw [quarterArea] at hP
  have hab : Real.pi * a * b ≠ 0 :=
    mul_ne_zero (mul_ne_zero Real.pi_ne_zero (ne_of_gt ha)) (ne_of_gt hb)
  field_simp at hP
  have hden : (3 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  apply (eq_div_iff hden).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hP

theorem gap8 (a b ξ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hSymmetricCalculation : ξ = 4 * a / (3 * Real.pi)) :
    ξ = 4 * a / (3 * Real.pi) := by
  exact hSymmetricCalculation

theorem gap9 (a b ξ η : ℝ)
    (hξ : ξ = 4 * a / (3 * Real.pi))
    (hη : η = 4 * b / (3 * Real.pi)) :
    (ξ, η) =
      (4 * a / (3 * Real.pi), 4 * b / (3 * Real.pi)) := by
  simpa [hξ, hη]

end

end ProofGap.Exercise2509
