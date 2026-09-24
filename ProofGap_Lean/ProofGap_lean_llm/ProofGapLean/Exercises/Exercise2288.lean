import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2288

noncomputable section

def modeProduct (n m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) *
    Complex.exp (-Complex.I * (m : ℂ) * (x : ℂ))

def innerProduct (n m : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..2 * Real.pi, modeProduct n m x

private theorem complexExpIntMul (k : ℤ) (x : ℝ) :
    Complex.exp (Complex.I * (k : ℂ) * (x : ℂ)) =
      (Real.cos ((k : ℝ) * x) : ℂ) +
        Complex.I * Real.sin ((k : ℝ) * x) := by
  have harg :
      Complex.I * (k : ℂ) * (x : ℂ) =
        ((((k : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
    norm_num
    ring
  rw [harg]
  simp [Complex.exp_mul_I] <;> ring

private theorem complexExpNegIntMul (k : ℤ) (x : ℝ) :
    Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ)) =
      (Real.cos ((k : ℝ) * x) : ℂ) -
        Complex.I * Real.sin ((k : ℝ) * x) := by
  have harg :
      -Complex.I * (k : ℂ) * (x : ℂ) =
        Complex.I * ((-k : ℤ) : ℂ) * (x : ℂ) := by
    norm_num
  rw [harg, complexExpIntMul (-k) x]
  have hreal :
      (((-k : ℤ) : ℝ) * x) = -((k : ℝ) * x) := by
    norm_num
  rw [hreal, Real.cos_neg, Real.sin_neg]
  simp [sub_eq_add_neg]

private theorem trigIntegralsIntMulEqZero (k : ℤ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..2 * Real.pi,
        Real.cos ((k : ℝ) * x)) = 0 ∧
      (∫ x in (0 : ℝ)..2 * Real.pi,
        Real.sin ((k : ℝ) * x)) = 0 := by
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  have hcosDeriv (x : ℝ) :
      HasDerivAt
        (fun y : ℝ => Real.sin ((k : ℝ) * y) / (k : ℝ))
        (Real.cos ((k : ℝ) * x)) x := by
    convert ((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (k : ℝ))).div_const (k : ℝ) using 1 <;>
      field_simp [hkR] <;> ring
  have hsinDeriv (x : ℝ) :
      HasDerivAt
        (fun y : ℝ => -Real.cos ((k : ℝ) * y) / (k : ℝ))
        (Real.sin ((k : ℝ) * x)) x := by
    convert (((Real.hasDerivAt_cos ((k : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (k : ℝ))).neg.div_const (k : ℝ)) using 1 <;>
      field_simp [hkR] <;> ring
  have hcosInt : IntervalIntegrable
      (fun x : ℝ => Real.cos ((k : ℝ) * x))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hsinInt : IntervalIntegrable
      (fun x : ℝ => Real.sin ((k : ℝ) * x))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hsinEnd : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    convert Real.sin_int_mul_pi (2 * k) using 1 <;> norm_num <;> ring
  constructor
  · calc
      (∫ x in (0 : ℝ)..2 * Real.pi,
          Real.cos ((k : ℝ) * x)) =
          Real.sin ((k : ℝ) * (2 * Real.pi)) / (k : ℝ) -
            Real.sin ((k : ℝ) * 0) / (k : ℝ) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hcosDeriv x) hcosInt
      _ = 0 := by
        simp [hsinEnd]
  · calc
      (∫ x in (0 : ℝ)..2 * Real.pi,
          Real.sin ((k : ℝ) * x)) =
          -Real.cos ((k : ℝ) * (2 * Real.pi)) / (k : ℝ) -
            (-Real.cos ((k : ℝ) * 0) / (k : ℝ)) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hsinDeriv x) hsinInt
      _ = 0 := by
        simp [Real.cos_int_mul_two_pi]

private theorem intervalIntegralOfRealEqZero
    (f : ℝ → ℝ) (a b : ℝ)
    (h : (∫ x in a..b, f x) = 0) :
    (∫ x in a..b, (f x : ℂ)) = 0 := by
  calc
    (∫ x in a..b, (f x : ℂ)) =
        ∫ x in a..b, f x • (1 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp
    _ = (∫ x in a..b, f x) • (1 : ℂ) := by
      simpa only using
        (intervalIntegral.integral_smul_const
          (μ := MeasureTheory.volume) (a := a) (b := b)
          (f := f) (c := (1 : ℂ)))
    _ = 0 := by
      rw [h]
      simp

theorem gap1 (n m : ℤ) (h : m = n) :
    innerProduct n m = ∫ _x in (0 : ℝ)..2 * Real.pi, (1 : ℂ) := by
  subst m
  unfold innerProduct
  apply intervalIntegral.integral_congr
  intro x hx
  change
    Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) *
        Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)) = 1
  rw [← Complex.exp_add]
  have hz :
      Complex.I * (n : ℂ) * (x : ℂ) +
          -Complex.I * (n : ℂ) * (x : ℂ) = 0 := by
    ring
  rw [hz, Complex.exp_zero]

theorem gap2 (n m : ℤ) (h : m = n) :
    (∫ _x in (0 : ℝ)..2 * Real.pi, (1 : ℂ)) = (2 * Real.pi : ℝ) := by
  rw [intervalIntegral.integral_const]
  calc
    (2 * Real.pi - 0) • (1 : ℂ) =
        algebraMap ℝ ℂ (2 * Real.pi - 0) * 1 :=
      Algebra.smul_def (2 * Real.pi - 0) (1 : ℂ)
    _ = (2 * Real.pi : ℝ) := by
      simp

theorem gap3 (n m : ℤ) (h : m = n) :
    innerProduct n m = (2 * Real.pi : ℝ) := by
  calc
    innerProduct n m = ∫ _x in (0 : ℝ)..2 * Real.pi, (1 : ℂ) := gap1 n m h
    _ = (2 * Real.pi : ℝ) := gap2 n m h

theorem gap4 (n m : ℤ) (h : m ≠ n) :
    innerProduct n m =
      ∫ x in (0 : ℝ)..2 * Real.pi,
        ((Real.cos ((n : ℝ) * x) : ℂ) +
            Complex.I * Real.sin ((n : ℝ) * x)) *
          ((Real.cos ((m : ℝ) * x) : ℂ) -
            Complex.I * Real.sin ((m : ℝ) * x)) := by
  unfold innerProduct
  apply intervalIntegral.integral_congr
  intro x hx
  unfold modeProduct
  rw [complexExpIntMul n x, complexExpNegIntMul m x]

theorem gap5 (n m : ℤ) (h : m ≠ n) :
    innerProduct n m =
      (∫ x in (0 : ℝ)..2 * Real.pi,
          (Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ)) -
        Complex.I * ∫ x in (0 : ℝ)..2 * Real.pi,
          (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ) := by
  have hprod (x : ℝ) :
      modeProduct n m x =
        (Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ) -
          Complex.I * (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ) := by
    unfold modeProduct
    rw [← Complex.exp_add]
    have harg :
        Complex.I * (n : ℂ) * (x : ℂ) +
            -Complex.I * (m : ℂ) * (x : ℂ) =
          -Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ) := by
      norm_num <;> ring
    rw [harg, complexExpNegIntMul (m - n) x]
  have hc : IntervalIntegrable
      (fun x : ℝ => (Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hs : IntervalIntegrable
      (fun x : ℝ => (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hIs : IntervalIntegrable
      (fun x : ℝ => Complex.I *
        (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    hs.const_mul Complex.I
  have hmul :
      (∫ x in (0 : ℝ)..2 * Real.pi,
        Complex.I * (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ)) =
        Complex.I * ∫ x in (0 : ℝ)..2 * Real.pi,
          (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ) := by
    simpa only using
      (intervalIntegral.integral_const_mul
        (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := 2 * Real.pi)
        (r := Complex.I)
        (f := fun x : ℝ =>
          (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ)))
  calc
    innerProduct n m =
        ∫ x in (0 : ℝ)..2 * Real.pi,
          ((Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ) -
            Complex.I * (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ)) := by
      unfold innerProduct
      apply intervalIntegral.integral_congr
      intro x hx
      exact hprod x
    _ =
        (∫ x in (0 : ℝ)..2 * Real.pi,
          (Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ)) -
        (∫ x in (0 : ℝ)..2 * Real.pi,
          Complex.I * (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ)) := by
      rw [intervalIntegral.integral_sub hc hIs]
    _ =
        (∫ x in (0 : ℝ)..2 * Real.pi,
          (Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ)) -
        Complex.I * ∫ x in (0 : ℝ)..2 * Real.pi,
          (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ) := by
      rw [hmul]

theorem gap6 (n m : ℤ) (h : m ≠ n) :
    (∫ x in (0 : ℝ)..2 * Real.pi,
        (Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ)) -
      Complex.I * (∫ x in (0 : ℝ)..2 * Real.pi,
        (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ)) = 0 := by
  have hk : m - n ≠ 0 := sub_ne_zero.mpr h
  obtain ⟨hc, hs⟩ := trigIntegralsIntMulEqZero (m - n) hk
  have hcC :
      (∫ x in (0 : ℝ)..2 * Real.pi,
        (Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ)) = 0 :=
    intervalIntegralOfRealEqZero
      (fun x : ℝ => Real.cos (((m - n : ℤ) : ℝ) * x))
      (0 : ℝ) (2 * Real.pi) hc
  have hsC :
      (∫ x in (0 : ℝ)..2 * Real.pi,
        (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ)) = 0 :=
    intervalIntegralOfRealEqZero
      (fun x : ℝ => Real.sin (((m - n : ℤ) : ℝ) * x))
      (0 : ℝ) (2 * Real.pi) hs
  rw [hcC, hsC]
  simp

theorem gap7 (n m : ℤ) (h : m ≠ n) :
    innerProduct n m = 0 := by
  calc
    innerProduct n m =
        (∫ x in (0 : ℝ)..2 * Real.pi,
          (Real.cos (((m - n : ℤ) : ℝ) * x) : ℂ)) -
        Complex.I * ∫ x in (0 : ℝ)..2 * Real.pi,
          (Real.sin (((m - n : ℤ) : ℝ) * x) : ℂ) := gap5 n m h
    _ = 0 := gap6 n m h

theorem gap8 (n m : ℤ) :
    innerProduct n m =
      if m = n then (2 * Real.pi : ℝ) else 0 := by
  by_cases h : m = n
  · rw [if_pos h]
    exact gap3 n m h
  · rw [if_neg h]
    exact gap7 n m h

end

end ProofGap.Exercise2288
