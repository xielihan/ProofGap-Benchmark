import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4247

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def curveMap (a h t : ℝ) : Vec3 :=
  (a * Real.cos t, a * Real.sin t, h / (2 * Real.pi) * t)

def curve (a h : ℝ) : Set Vec3 :=
  curveMap a h '' Set.Icc 0 (2 * Real.pi)

def rawSpeed (a h t : ℝ) : ℝ :=
  Real.sqrt
    (a ^ 2 * Real.sin t ^ 2 + a ^ 2 * Real.cos t ^ 2 +
      h ^ 2 / (4 * Real.pi ^ 2))

def speed (a h : ℝ) : ℝ :=
  Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) / (2 * Real.pi)

def inertiaX (a h : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    ((curveMap a h t).2.1 ^ 2 + (curveMap a h t).2.2 ^ 2) *
      speed a h

def inertiaY (a h : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    ((curveMap a h t).1 ^ 2 + (curveMap a h t).2.2 ^ 2) *
      speed a h

def inertiaZ (a h : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    ((curveMap a h t).1 ^ 2 + (curveMap a h t).2.1 ^ 2) *
      speed a h

private theorem hasDerivAtSinSqPrimitive (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => x / 2 - Real.sin x * Real.cos x / 2)
      (Real.sin t ^ 2) t := by
  convert ((hasDerivAt_id t).div_const 2).sub
    (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).div_const 2) using 1
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem hasDerivAtCosSqPrimitive (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => x / 2 + Real.sin x * Real.cos x / 2)
      (Real.cos t ^ 2) t := by
  convert ((hasDerivAt_id t).div_const 2).add
    (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).div_const 2) using 1
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem hasDerivAtSqPrimitive (t : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 3 / 3) (t ^ 2) t := by
  convert ((hasDerivAt_id t).pow 3).div_const 3 using 1
  simp [id_eq]

private theorem integralSinSqAndSq (A B C : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      (A * Real.sin t ^ 2 + B * t ^ 2) * C) =
      (A * Real.pi + B * (8 * Real.pi ^ 3 / 3)) * C := by
  let F : ℝ → ℝ := fun t =>
    (A * (t / 2 - Real.sin t * Real.cos t / 2) +
      B * (t ^ 3 / 3)) * C
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
      (A * Real.sin t ^ 2 + B * t ^ 2) * C) =
        F (2 * Real.pi) - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _
        dsimp [F]
        convert (((hasDerivAtSinSqPrimitive t).const_mul A).add
          ((hasDerivAtSqPrimitive t).const_mul B)).mul_const C using 1 <;> ring
      · have hsin : Continuous (fun y : ℝ => A * Real.sin y ^ 2) :=
          continuous_const.mul (Real.continuous_sin.pow 2)
        have hsq : Continuous (fun y : ℝ => B * y ^ 2) :=
          continuous_const.mul (continuous_id.pow 2)
        have hconst : Continuous (fun _ : ℝ => C) := continuous_const
        exact ((hsin.add hsq).mul hconst).intervalIntegrable
          (μ := MeasureTheory.volume) 0 (2 * Real.pi)
    _ = (A * Real.pi + B * (8 * Real.pi ^ 3 / 3)) * C := by
      dsimp [F]
      rw [Real.sin_two_pi, Real.sin_zero, Real.cos_two_pi, Real.cos_zero]
      ring

private theorem integralCosSqAndSq (A B C : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      (A * Real.cos t ^ 2 + B * t ^ 2) * C) =
      (A * Real.pi + B * (8 * Real.pi ^ 3 / 3)) * C := by
  let F : ℝ → ℝ := fun t =>
    (A * (t / 2 + Real.sin t * Real.cos t / 2) +
      B * (t ^ 3 / 3)) * C
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
      (A * Real.cos t ^ 2 + B * t ^ 2) * C) =
        F (2 * Real.pi) - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _
        dsimp [F]
        convert (((hasDerivAtCosSqPrimitive t).const_mul A).add
          ((hasDerivAtSqPrimitive t).const_mul B)).mul_const C using 1 <;> ring
      · have hcos : Continuous (fun y : ℝ => A * Real.cos y ^ 2) :=
          continuous_const.mul (Real.continuous_cos.pow 2)
        have hsq : Continuous (fun y : ℝ => B * y ^ 2) :=
          continuous_const.mul (continuous_id.pow 2)
        have hconst : Continuous (fun _ : ℝ => C) := continuous_const
        exact ((hcos.add hsq).mul hconst).intervalIntegrable
          (μ := MeasureTheory.volume) 0 (2 * Real.pi)
    _ = (A * Real.pi + B * (8 * Real.pi ^ 3 / 3)) * C := by
      dsimp [F]
      rw [Real.sin_two_pi, Real.sin_zero, Real.cos_two_pi, Real.cos_zero]
      ring

theorem gap1 (a h t : ℝ) :
    rawSpeed a h t =
      Real.sqrt
        (a ^ 2 * Real.sin t ^ 2 + a ^ 2 * Real.cos t ^ 2 +
          h ^ 2 / (4 * Real.pi ^ 2)) := by
  rfl

theorem gap2 (a h t : ℝ) :
    rawSpeed a h t = speed a h := by
  unfold rawSpeed speed
  have htrig :
      a ^ 2 * Real.sin t ^ 2 + a ^ 2 * Real.cos t ^ 2 = a ^ 2 := by
    calc
      a ^ 2 * Real.sin t ^ 2 + a ^ 2 * Real.cos t ^ 2 =
          a ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = a ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hN : 0 ≤ 4 * Real.pi ^ 2 * a ^ 2 + h ^ 2 := by positivity
  have hsqrt :
      Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) ^ 2 =
        4 * Real.pi ^ 2 * a ^ 2 + h ^ 2 :=
    Real.sq_sqrt hN
  have harg :
      a ^ 2 * Real.sin t ^ 2 + a ^ 2 * Real.cos t ^ 2 +
          h ^ 2 / (4 * Real.pi ^ 2) =
        (Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) /
          (2 * Real.pi)) ^ 2 := by
    rw [htrig, div_pow, hsqrt]
    field_simp [Real.pi_ne_zero]
    ring
  have hnonneg :
      0 ≤ Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) /
        (2 * Real.pi) := by positivity
  rw [harg, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

theorem gap3 (a h : ℝ) :
    inertiaX a h =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        ((curveMap a h t).2.1 ^ 2 + (curveMap a h t).2.2 ^ 2) *
          speed a h := by
  rfl

theorem gap4 (a h : ℝ) :
    inertiaX a h =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        (a ^ 2 * Real.sin t ^ 2 +
          h ^ 2 / (4 * Real.pi ^ 2) * t ^ 2) *
            (Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) /
              (2 * Real.pi)) := by
  rw [gap3]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [curveMap, speed]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap5 (a h : ℝ) :
    inertiaX a h =
      (a ^ 2 / 2 + h ^ 2 / 3) *
        Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) := by
  rw [gap4, integralSinSqAndSq]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap6 (a h : ℝ) :
    inertiaY a h =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        ((curveMap a h t).1 ^ 2 + (curveMap a h t).2.2 ^ 2) *
          speed a h := by
  rfl

theorem gap7 (a h : ℝ) :
    inertiaY a h =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        (a ^ 2 * Real.cos t ^ 2 +
          h ^ 2 / (4 * Real.pi ^ 2) * t ^ 2) *
            (Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) /
              (2 * Real.pi)) := by
  rw [gap6]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [curveMap, speed]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap8 (a h : ℝ) :
    inertiaY a h =
      (a ^ 2 / 2 + h ^ 2 / 3) *
        Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) := by
  rw [gap7, integralCosSqAndSq]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap9 (a h : ℝ) :
    inertiaZ a h =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        ((curveMap a h t).1 ^ 2 + (curveMap a h t).2.1 ^ 2) *
          speed a h := by
  rfl

theorem gap10 (a h : ℝ) :
    inertiaZ a h =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        a ^ 2 *
          (Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) /
            (2 * Real.pi)) := by
  rw [gap9]
  apply intervalIntegral.integral_congr
  intro t _
  have hxy :
      (a * Real.cos t) ^ 2 + (a * Real.sin t) ^ 2 = a ^ 2 := by
    calc
      (a * Real.cos t) ^ 2 + (a * Real.sin t) ^ 2 =
          a ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = a ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
  simp [curveMap, speed, hxy]

theorem gap11 (a h : ℝ) :
    inertiaZ a h =
      a ^ 2 * Real.sqrt (4 * Real.pi ^ 2 * a ^ 2 + h ^ 2) := by
  rw [gap10]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

end

end ProofGap.Exercise4247
