import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4187

noncomputable section

open Filter MeasureTheory
open scoped Interval

def disk : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

def logarithmicIntegrand (z : ℝ × ℝ) : ℝ :=
  Real.log (1 / Real.sqrt (z.1 ^ 2 + z.2 ^ 2))

def integralValue : ℝ :=
  ∫ z in disk, logarithmicIntegrand z

private theorem disk_measurable : MeasurableSet disk := by
  exact
    (isClosed_le
      ((continuous_fst.pow 2).add (continuous_snd.pow 2))
      continuous_const).measurableSet

private theorem polar_pointwise
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • disk.indicator logarithmicIntegrand
        (polarCoord.symm p) =
      (Set.Iic (1 : ℝ)).indicator
          (fun r => r * Real.log (1 / r)) p.1 *
        (1 : ℝ) := by
  rcases p with ⟨r, theta⟩
  have hr : 0 < r := hp.1
  have htrig :
      (r * Real.cos theta) ^ 2 +
          (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 *
          (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      polarCoord.symm (r, theta) ∈ disk ↔ r ≤ 1 := by
    rw [polarCoord_symm_apply]
    simp only [disk, Set.mem_setOf_eq, htrig]
    constructor
    · intro h
      nlinarith [sq_nonneg (r + 1)]
    · intro h
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h)]
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  split_ifs with h
  · rw [polarCoord_symm_apply]
    simp only [logarithmicIntegrand, htrig, Real.sqrt_sq hr.le]
    ring
  · simp

private theorem angular_set_value :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  calc
    _ = ∫ theta in Set.Ioc (-Real.pi) Real.pi, (1 : ℝ) :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun _ : ℝ => (1 : ℝ))).symm
    _ = ∫ theta in -Real.pi..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = 2 * Real.pi := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

private theorem angular_interval_value :
    (∫ theta in (0 : ℝ)..2 * Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem radial_set_integral :
    (∫ r in Set.Ioi (0 : ℝ),
        (Set.Iic (1 : ℝ)).indicator
          (fun r => r * Real.log (1 / r)) r) =
      ∫ r in (0 : ℝ)..1, r * Real.log (1 / r) := by
  rw [setIntegral_indicator measurableSet_Iic]
  have hinter :
      Set.Ioi (0 : ℝ) ∩ Set.Iic 1 = Set.Ioc (0 : ℝ) 1 := by
    ext r
    simp
  rw [hinter, intervalIntegral.integral_of_le zero_le_one]

private theorem integralValue_polar :
    integralValue =
      (∫ theta in (0 : ℝ)..2 * Real.pi, (1 : ℝ)) *
        ∫ r in (0 : ℝ)..1, r * Real.log (1 / r) := by
  have hpolar := integral_comp_polarCoord_symm
    (disk.indicator logarithmicIntegrand)
  rw [integral_indicator disk_measurable] at hpolar
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • disk.indicator logarithmicIntegrand
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic (1 : ℝ)).indicator
              (fun r => r * Real.log (1 / r)) r) *
          ∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic (1 : ℝ)).indicator
              (fun r => r * Real.log (1 / r)) p.1 *
                (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp
        exact polar_pointwise p hp
      _ = _ := by
        exact MeasureTheory.setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic (1 : ℝ)).indicator
              (fun r => r * Real.log (1 / r)) r)
          (fun _ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  rw [hprod, radial_set_integral, angular_set_value] at hpolar
  rw [integralValue, ← hpolar, angular_interval_value]
  ring

private theorem radial_inv_eq_neg :
    (∫ r in (0 : ℝ)..1, r * Real.log (1 / r)) =
      -(∫ r in (0 : ℝ)..1, r * Real.log r) := by
  calc
    _ = ∫ r in (0 : ℝ)..1, -(r * Real.log r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      simp only
      rw [one_div, Real.log_inv]
      ring
    _ = _ := intervalIntegral.integral_neg

private def radialPrimitive (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * r ^ 2 * Real.log r - (1 / 4 : ℝ) * r ^ 2

private theorem radial_log_value :
    (∫ r in (0 : ℝ)..1, r * Real.log r) = -(1 / 4 : ℝ) := by
  have hderiv :
      ∀ r ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt radialPrimitive (r * Real.log r) r := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr.1
    have hsq :
        HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
      convert (hasDerivAt_id r).pow 2 using 1 <;>
        simp only [id_eq] <;> ring
    unfold radialPrimitive
    have hprod :=
      hsq.mul (Real.hasDerivAt_log hr0)
    have hfinal :=
      (hprod.const_mul (1 / 2 : ℝ)).sub
        (hsq.const_mul (1 / 4 : ℝ))
    convert hfinal using 1
    · funext x
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring
    · field_simp [hr0]
      ring
  have hint :
      IntervalIntegrable (fun r : ℝ => r * Real.log r)
        volume 0 1 := by
    simpa using
      (intervalIntegral.intervalIntegrable_log'
        (a := (0 : ℝ)) (b := 1)).continuousOn_mul
          continuous_id.continuousOn
  have hleft :
      Tendsto radialPrimitive
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hlogpow :=
      tendsto_log_mul_rpow_nhdsGT_zero (show (0 : ℝ) < 2 by norm_num)
    have hlogsq :
        Tendsto (fun r : ℝ => r ^ 2 * Real.log r)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      convert hlogpow using 1
      · funext r
        rw [Real.rpow_two]
        ring
    have hsq :
        Tendsto (fun r : ℝ => r ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hcont : ContinuousAt (fun r : ℝ => r ^ 2) 0 := by
        fun_prop
      simpa using
        tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto
    convert
      ((hlogsq.const_mul (1 / 2 : ℝ)).sub
        (hsq.const_mul (1 / 4 : ℝ))) using 1
    · funext r
      simp only [radialPrimitive]
      ring
    · norm_num
  have hright :
      Tendsto radialPrimitive
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (-(1 / 4 : ℝ))) := by
    have hcont : ContinuousAt radialPrimitive 1 := by
      unfold radialPrimitive
      exact
        (((continuousAt_const.mul (continuousAt_id.pow 2)).mul
          (Real.continuousAt_log one_ne_zero)).sub
            (continuousAt_const.mul (continuousAt_id.pow 2)))
    convert tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto using 1
    norm_num [radialPrimitive]
  simpa [radialPrimitive] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (a := (0 : ℝ)) (b := 1) (f := radialPrimitive)
      (f' := fun r : ℝ => r * Real.log r)
      (fa := (0 : ℝ)) (fb := (-(1 / 4 : ℝ)))
      zero_lt_one hderiv hint hleft hright)

theorem gap1 :
    integralValue =
      (∫ theta in (0 : ℝ)..2 * Real.pi, (1 : ℝ)) *
        ∫ r in (0 : ℝ)..1, r * Real.log (1 / r) := by
  exact integralValue_polar

theorem gap2 :
    integralValue =
      -2 * Real.pi *
        ∫ r in (0 : ℝ)..1, r * Real.log r := by
  rw [gap1, angular_interval_value, radial_inv_eq_neg]
  ring

theorem gap3 :
    integralValue = Real.pi / 2 := by
  rw [gap2, radial_log_value]
  ring

end

end ProofGap.Exercise4187
