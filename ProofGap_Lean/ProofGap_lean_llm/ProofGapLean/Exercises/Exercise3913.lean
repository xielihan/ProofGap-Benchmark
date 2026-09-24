import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3913

noncomputable section

open MeasureTheory
open scoped Interval

def I0 : ℝ :=
  1 / Real.pi ^ 2 *
    ∫ x in (0 : ℝ)..Real.pi,
      ∫ y in (0 : ℝ)..Real.pi,
        Real.sin x ^ 2 * Real.sin y ^ 2

def sinSqPrimitive (x : ℝ) : ℝ :=
  x / 2 - 1 / 4 * Real.sin (2 * x)

theorem gap1 :
    I0 =
      1 / Real.pi ^ 2 *
        ∫ x in (0 : ℝ)..Real.pi,
          ∫ y in (0 : ℝ)..Real.pi,
            Real.sin x ^ 2 * Real.sin y ^ 2 := by
  rfl

theorem gap2 :
    I0 =
      1 / Real.pi ^ 2 *
        (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) ^ 2 := by
  unfold I0
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const]
  ring

theorem gap3 :
    1 / Real.pi ^ 2 *
        (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) ^ 2 =
      1 / Real.pi ^ 2 *
        (sinSqPrimitive Real.pi - sinSqPrimitive 0) ^ 2 := by
  have hderiv : ∀ x : ℝ, HasDerivAt sinSqPrimitive (Real.sin x ^ 2) x := by
    intro x
    have hsin :
        HasDerivAt (fun t : ℝ => Real.sin (2 * t))
          (Real.cos (2 * x) * 2) x := by
      simpa only [Function.comp_apply, mul_one] using
        (Real.hasDerivAt_sin (2 * x)).comp x
          ((hasDerivAt_id x).const_mul 2)
    unfold sinSqPrimitive
    convert ((hasDerivAt_id x).div_const 2).sub
      (hsin.const_mul (1 / 4)) using 1
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have heval :
      (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) =
        sinSqPrimitive Real.pi - sinSqPrimitive 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x)
      ((Real.continuous_sin.pow 2).intervalIntegrable 0 Real.pi)
  rw [heval]

theorem gap4 :
    1 / Real.pi ^ 2 *
        (sinSqPrimitive Real.pi - sinSqPrimitive 0) ^ 2 =
      1 / 4 := by
  simp only [sinSqPrimitive, Real.sin_zero, Real.sin_two_pi, mul_zero,
    sub_zero, zero_div]
  field_simp [ne_of_gt Real.pi_pos]
  <;> ring

theorem gap5 :
    I0 = 1 / 4 := by
  rw [gap2, gap3, gap4]

end

end ProofGap.Exercise3913
