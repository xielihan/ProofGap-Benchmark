import ProofGapLean.Prelude.Elementary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open scoped Interval

namespace ProofGap.Exercise2241

noncomputable section

theorem gap1 :
    (∫ x in (0 : ℝ)..2 * Real.pi, x ^ 2 * Real.cos x) =
      ((2 * Real.pi) ^ 2 * Real.sin (2 * Real.pi) -
        0 ^ 2 * Real.sin 0) -
      2 * ∫ x in (0 : ℝ)..2 * Real.pi, x * Real.sin x := by
  have h :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (u := fun x : ℝ => x ^ 2) (u' := fun x : ℝ => 2 * x)
      (v := fun x : ℝ => Real.sin x) (v' := fun x : ℝ => Real.cos x)
      (fun x _ => by
        simpa [pow_two, two_mul] using
          (hasDerivAt_id x).mul (hasDerivAt_id x))
      (fun x _ => Real.hasDerivAt_sin x)
      ((continuous_const.mul continuous_id :
          Continuous (fun x : ℝ => (2 : ℝ) * x)).intervalIntegrable _ _)
      (Real.continuous_cos.intervalIntegrable _ _)
  simpa only [intervalIntegral.integral_const_mul, mul_assoc] using h

theorem gap2 :
    ((2 * Real.pi) ^ 2 * Real.sin (2 * Real.pi) -
        0 ^ 2 * Real.sin 0) -
        2 * (∫ x in (0 : ℝ)..2 * Real.pi, x * Real.sin x) =
      2 *
        (((2 * Real.pi) * Real.cos (2 * Real.pi) - 0 * Real.cos 0) -
          ∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x) := by
  have h :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (u := fun x : ℝ => x) (u' := fun _ : ℝ => 1)
      (v := fun x : ℝ => Real.cos x) (v' := fun x : ℝ => -Real.sin x)
      (fun x _ => hasDerivAt_id x)
      (fun x _ => Real.hasDerivAt_cos x)
      ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable _ _)
      (Real.continuous_sin.neg.intervalIntegrable _ _)
  have h' :
      -(∫ x in (0 : ℝ)..2 * Real.pi, x * Real.sin x) =
        ((2 * Real.pi) * Real.cos (2 * Real.pi) - 0 * Real.cos 0) -
          ∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x := by
    simpa only [mul_neg, intervalIntegral.integral_neg, one_mul] using h
  calc
    ((2 * Real.pi) ^ 2 * Real.sin (2 * Real.pi) -
          0 ^ 2 * Real.sin 0) -
        2 * (∫ x in (0 : ℝ)..2 * Real.pi, x * Real.sin x) =
        2 * (-(∫ x in (0 : ℝ)..2 * Real.pi, x * Real.sin x)) := by
          rw [Real.sin_two_pi]
          ring
    _ = 2 *
        (((2 * Real.pi) * Real.cos (2 * Real.pi) - 0 * Real.cos 0) -
          ∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x) := by
          rw [h']

theorem gap3 :
    2 *
        (((2 * Real.pi) * Real.cos (2 * Real.pi) - 0 * Real.cos 0) -
          ∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x) =
      4 * Real.pi := by
  have h :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (u := fun _ : ℝ => 1) (u' := fun _ : ℝ => 0)
      (v := fun x : ℝ => Real.sin x) (v' := fun x : ℝ => Real.cos x)
      (fun x _ => hasDerivAt_const x (1 : ℝ))
      (fun x _ => Real.hasDerivAt_sin x)
      ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).intervalIntegrable _ _)
      (Real.continuous_cos.intervalIntegrable _ _)
  have hc : (∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x) = 0 := by
    simpa [Real.sin_two_pi] using h
  rw [hc, Real.cos_two_pi]
  ring

theorem gap4 :
    (∫ x in (0 : ℝ)..2 * Real.pi, x ^ 2 * Real.cos x) =
      4 * Real.pi := by
  calc
    (∫ x in (0 : ℝ)..2 * Real.pi, x ^ 2 * Real.cos x) =
        ((2 * Real.pi) ^ 2 * Real.sin (2 * Real.pi) -
          0 ^ 2 * Real.sin 0) -
        2 * ∫ x in (0 : ℝ)..2 * Real.pi, x * Real.sin x := gap1
    _ = 2 *
        (((2 * Real.pi) * Real.cos (2 * Real.pi) - 0 * Real.cos 0) -
          ∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x) := gap2
    _ = 4 * Real.pi := gap3

end

end ProofGap.Exercise2241
