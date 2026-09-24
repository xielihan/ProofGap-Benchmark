import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4246

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ

def curveMap (t : ℝ) : Vec3 :=
  (Real.exp t * Real.cos t, Real.exp t * Real.sin t, Real.exp t)

def curve : Set Vec3 :=
  curveMap '' Set.Iic 0

def rawSpeed (t : ℝ) : ℝ :=
  Real.sqrt
    (Real.exp (2 * t) * (Real.cos t - Real.sin t) ^ 2 +
      Real.exp (2 * t) * (Real.sin t + Real.cos t) ^ 2 +
      Real.exp (2 * t))

def speed (t : ℝ) : ℝ :=
  Real.sqrt 3 * Real.exp t

def mass : ℝ :=
  ∫ t in Set.Iic (0 : ℝ), speed t

def xCentroid : ℝ :=
  1 / mass *
    ∫ t in Set.Iic (0 : ℝ), (curveMap t).1 * speed t

def yCentroid : ℝ :=
  1 / mass *
    ∫ t in Set.Iic (0 : ℝ), (curveMap t).2.1 * speed t

def zCentroid : ℝ :=
  1 / mass *
    ∫ t in Set.Iic (0 : ℝ), (curveMap t).2.2 * speed t

def xPrimitive (t : ℝ) : ℝ :=
  (2 * Real.cos t + Real.sin t) / 5 * Real.exp (2 * t)

def yPrimitive (t : ℝ) : ℝ :=
  (2 * Real.sin t - Real.cos t) / 5 * Real.exp (2 * t)

private theorem complexIntegral :
    (∫ t in Set.Iic (0 : ℝ),
      Complex.exp (((2 : ℂ) + Complex.I) * (t : ℂ))) =
        (2 : ℂ) / 5 - (1 : ℂ) / 5 * Complex.I := by
  rw [integral_exp_mul_complex_Iic
    (a := (2 : ℂ) + Complex.I) (by norm_num)]
  norm_num [Complex.div_re, Complex.div_im, Complex.ext_iff,
    Complex.normSq_apply]

private theorem cosIntegral :
    (∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) * Real.cos t) =
      2 / 5 := by
  have hint := integrableOn_exp_mul_complex_Iic
    (a := (2 : ℂ) + Complex.I) (by norm_num) 0
  calc
    (∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) * Real.cos t) =
        ∫ t in Set.Iic (0 : ℝ),
          RCLike.re
            (Complex.exp (((2 : ℂ) + Complex.I) * (t : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro t ht
      change Real.exp (2 * t) * Real.cos t =
        RCLike.re
          (Complex.exp (((2 : ℂ) + Complex.I) * (t : ℂ)))
      rw [show ((2 : ℂ) + Complex.I) * (t : ℂ) =
        ((2 * t : ℝ) : ℂ) + (t : ℂ) * Complex.I by
          push_cast
          ring]
      simp [Complex.exp_add, Complex.exp_mul_I,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re]
      rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by
        push_cast
        ring]
      rw [Complex.exp_ofReal_re, Complex.exp_ofReal_im]
      ring
    _ = RCLike.re
        (∫ t in Set.Iic (0 : ℝ),
          Complex.exp (((2 : ℂ) + Complex.I) * (t : ℂ))) :=
      integral_re hint
    _ = 2 / 5 := by
      rw [complexIntegral]
      norm_num

private theorem sinIntegral :
    (∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) * Real.sin t) =
      -(1 / 5) := by
  have hint := integrableOn_exp_mul_complex_Iic
    (a := (2 : ℂ) + Complex.I) (by norm_num) 0
  calc
    (∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) * Real.sin t) =
        ∫ t in Set.Iic (0 : ℝ),
          RCLike.im
            (Complex.exp (((2 : ℂ) + Complex.I) * (t : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro t ht
      change Real.exp (2 * t) * Real.sin t =
        RCLike.im
          (Complex.exp (((2 : ℂ) + Complex.I) * (t : ℂ)))
      rw [show ((2 : ℂ) + Complex.I) * (t : ℂ) =
        ((2 * t : ℝ) : ℂ) + (t : ℂ) * Complex.I by
          push_cast
          ring]
      simp [Complex.exp_add, Complex.exp_mul_I,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re]
      rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by
        push_cast
        ring]
      rw [Complex.exp_ofReal_re, Complex.exp_ofReal_im]
      ring
    _ = RCLike.im
        (∫ t in Set.Iic (0 : ℝ),
          Complex.exp (((2 : ℂ) + Complex.I) * (t : ℂ))) :=
      integral_im hint
    _ = -(1 / 5) := by
      rw [complexIntegral]
      norm_num

private theorem rawSpeed_eq (t : ℝ) :
    rawSpeed t = Real.sqrt 3 * Real.exp t := by
  have hexp : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [show 2 * t = t + t by ring, Real.exp_add]
    ring
  have harg :
      Real.exp (2 * t) * (Real.cos t - Real.sin t) ^ 2 +
          Real.exp (2 * t) * (Real.sin t + Real.cos t) ^ 2 +
          Real.exp (2 * t) =
        3 * Real.exp t ^ 2 := by
    rw [hexp]
    nlinarith [Real.sin_sq_add_cos_sq t]
  unfold rawSpeed
  rw [harg, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
    Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos t)]

private theorem expProductCos (t : ℝ) :
    Real.exp t * Real.cos t * (Real.sqrt 3 * Real.exp t) =
      Real.sqrt 3 * (Real.exp (2 * t) * Real.cos t) := by
  rw [show 2 * t = t + t by ring, Real.exp_add]
  ring

private theorem expProductSin (t : ℝ) :
    Real.exp t * Real.sin t * (Real.sqrt 3 * Real.exp t) =
      Real.sqrt 3 * (Real.exp (2 * t) * Real.sin t) := by
  rw [show 2 * t = t + t by ring, Real.exp_add]
  ring

private theorem expProduct (t : ℝ) :
    Real.exp t * (Real.sqrt 3 * Real.exp t) =
      Real.sqrt 3 * Real.exp (2 * t) := by
  rw [show 2 * t = t + t by ring, Real.exp_add]
  ring

theorem gap1 (t : ℝ) :
    rawSpeed t =
      Real.sqrt
        (Real.exp (2 * t) * (Real.cos t - Real.sin t) ^ 2 +
          Real.exp (2 * t) * (Real.sin t + Real.cos t) ^ 2 +
          Real.exp (2 * t)) := by
  rfl

theorem gap2 (t : ℝ) :
    rawSpeed t = Real.sqrt 3 * Real.exp t := by
  exact rawSpeed_eq t

theorem gap3 :
    mass = Real.sqrt 3 := by
  unfold mass speed
  rw [integral_const_mul, integral_exp_Iic_zero, mul_one]

theorem gap4 :
    xCentroid =
      1 / mass *
        ∫ t in Set.Iic (0 : ℝ),
          Real.exp t * Real.cos t * (Real.sqrt 3 * Real.exp t) := by
  rfl

theorem gap5 :
    xCentroid =
      ∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) * Real.cos t := by
  have hsqrt : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hi :
      (∫ t in Set.Iic (0 : ℝ),
        (curveMap t).1 * speed t) =
      Real.sqrt 3 *
        ∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) * Real.cos t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    simpa [curveMap, speed] using expProductCos t
  unfold xCentroid
  rw [gap3, hi]
  field_simp [hsqrt]

theorem gap6 :
    xCentroid = xPrimitive 0 := by
  rw [gap5, cosIntegral]
  norm_num [xPrimitive]

theorem gap7 :
    xCentroid = 2 / 5 := by
  rw [gap6]
  norm_num [xPrimitive]

theorem gap8 :
    yCentroid =
      1 / mass *
        ∫ t in Set.Iic (0 : ℝ),
          Real.exp t * Real.sin t * (Real.sqrt 3 * Real.exp t) := by
  rfl

theorem gap9 :
    yCentroid =
      ∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) * Real.sin t := by
  have hsqrt : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hi :
      (∫ t in Set.Iic (0 : ℝ),
        (curveMap t).2.1 * speed t) =
      Real.sqrt 3 *
        ∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) * Real.sin t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    simpa [curveMap, speed] using expProductSin t
  unfold yCentroid
  rw [gap3, hi]
  field_simp [hsqrt]

theorem gap10 :
    yCentroid = yPrimitive 0 := by
  rw [gap9, sinIntegral]
  norm_num [yPrimitive]

theorem gap11 :
    yCentroid = -(1 / 5) := by
  rw [gap10]
  norm_num [yPrimitive]

theorem gap12 :
    zCentroid =
      1 / mass *
        ∫ t in Set.Iic (0 : ℝ),
          Real.exp t * (Real.sqrt 3 * Real.exp t) := by
  rfl

theorem gap13 :
    zCentroid =
      ∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) := by
  have hsqrt : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hi :
      (∫ t in Set.Iic (0 : ℝ),
        (curveMap t).2.2 * speed t) =
      Real.sqrt 3 *
        ∫ t in Set.Iic (0 : ℝ), Real.exp (2 * t) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    simpa [curveMap, speed] using expProduct t
  unfold zCentroid
  rw [gap3, hi]
  field_simp [hsqrt]

theorem gap14 :
    zCentroid = 1 / 2 := by
  rw [gap13, integral_exp_mul_Iic
    (a := (2 : ℝ)) (by norm_num) (0 : ℝ)]
  norm_num

end

end ProofGap.Exercise4246
