import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4073

noncomputable section

open MeasureTheory
open scoped Interval

def ellipse (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤ 1}

def pressure (a b p₀ : ℝ) (p : ℝ × ℝ) : ℝ :=
  p₀ * (1 - p.1 ^ 2 / a ^ 2 - p.2 ^ 2 / b ^ 2)

def averagePressure (a b p₀ : ℝ) : ℝ :=
  1 / (Real.pi * a * b) *
    ∫ p in ellipse a b, pressure a b p₀ p

private def unitDisk : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

private def scaleCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![a, 0; 0, b]).toContinuousLinearMap

private theorem scaleCLM_apply (a b : ℝ) (p : ℝ × ℝ) :
    scaleCLM a b p = (a * p.1, b * p.2) := by
  unfold scaleCLM
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  simp

private theorem det_scaleCLM (a b : ℝ) :
    (scaleCLM a b).det = a * b := by
  unfold scaleCLM
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

private theorem scale_image_unitDisk (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    scaleCLM a b '' unitDisk = ellipse a b := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hx : (a * p.1) ^ 2 / a ^ 2 = p.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * p.2) ^ 2 / b ^ 2 = p.2 ^ 2 := by
      field_simp [hb.ne']
    simpa [unitDisk, ellipse, scaleCLM_apply, hx, hy] using hp
  · intro hq
    let p : ℝ × ℝ := (q.1 / a, q.2 / b)
    have hmap : scaleCLM a b p = q := by
      rw [scaleCLM_apply]
      ext
      · dsimp [p]
        field_simp [ha.ne']
      · dsimp [p]
        field_simp [hb.ne']
    refine ⟨p, ?_, hmap⟩
    have hx : (q.1 / a) ^ 2 = q.1 ^ 2 / a ^ 2 := by ring
    have hy : (q.2 / b) ^ 2 = q.2 ^ 2 / b ^ 2 := by ring
    simpa [unitDisk, ellipse, p, hx, hy] using hq

private theorem scale_injOn (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Set.InjOn (scaleCLM a b) unitDisk := by
  intro p hp q hq heq
  have h1 : a * p.1 = a * q.1 := by
    simpa [scaleCLM_apply] using congrArg Prod.fst heq
  have h2 : b * p.2 = b * q.2 := by
    simpa [scaleCLM_apply] using congrArg Prod.snd heq
  ext
  · exact mul_left_cancel₀ ha.ne' h1
  · exact mul_left_cancel₀ hb.ne' h2

private theorem unitDisk_measurable : MeasurableSet unitDisk := by
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const |>.measurableSet

private theorem ellipse_integral_scaled (a b p₀ : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    (∫ p in ellipse a b, pressure a b p₀ p) =
      ∫ p in unitDisk, a * b * p₀ * (1 - p.1 ^ 2 - p.2 ^ 2) := by
  let g : ℝ × ℝ → ℝ := fun q => pressure a b p₀ q
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) unitDisk_measurable
      (f := scaleCLM a b) (f' := fun _ => scaleCLM a b)
      (fun p hp => (scaleCLM a b).hasFDerivAt.hasFDerivWithinAt)
      (scale_injOn a b ha hb) g
  rw [scale_image_unitDisk a b ha hb] at hchange
  have hab : 0 < a * b := mul_pos ha hb
  have hpoint (p : ℝ × ℝ) :
      |(scaleCLM a b).det| • g (scaleCLM a b p) =
        a * b * p₀ * (1 - p.1 ^ 2 - p.2 ^ 2) := by
    rw [det_scaleCLM, abs_of_pos hab]
    simp only [smul_eq_mul, g, pressure, scaleCLM_apply]
    have hx : (a * p.1) ^ 2 / a ^ 2 = p.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * p.2) ^ 2 / b ^ 2 = p.2 ^ 2 := by
      field_simp [hb.ne']
    rw [hx, hy]
    ring
  simpa only [hpoint] using hchange

private theorem polar_pointwise (a b p₀ : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    p.1 • unitDisk.indicator
        (fun q : ℝ × ℝ => a * b * p₀ * (1 - q.1 ^ 2 - q.2 ^ 2))
        (polarCoord.symm p) =
      (Set.Iic (1 : ℝ)).indicator
          (fun r => r * (a * b * p₀ * (1 - r ^ 2))) p.1 *
        (1 : ℝ) := by
  rcases p with ⟨r, theta⟩
  have hr : 0 < r := hp.1
  have htrig : (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 =
          r ^ 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      (polarCoord.symm (r, theta)) ∈ unitDisk ↔ r ≤ 1 := by
    rw [polarCoord_symm_apply]
    simp only [unitDisk, Set.mem_setOf_eq]
    rw [htrig]
    constructor
    · intro h
      nlinarith [sq_nonneg (r - 1)]
    · intro h
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h)]
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  split_ifs with h
  · rw [polarCoord_symm_apply]
    simp only
    rw [show
      1 - (r * Real.cos theta) ^ 2 - (r * Real.sin theta) ^ 2 =
        1 - ((r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2) by ring,
      htrig]
    ring
  · simp

private theorem angular_integral_one :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  calc
    (∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
        ∫ theta in Set.Ioc (-Real.pi) Real.pi, (1 : ℝ) := by
      exact (integral_Ioc_eq_integral_Ioo (f := fun _ : ℝ => (1 : ℝ))).symm
    _ = ∫ theta in -Real.pi..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = 2 * Real.pi := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

private theorem radial_set_integral (a b p₀ : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
        (Set.Iic (1 : ℝ)).indicator
          (fun r => r * (a * b * p₀ * (1 - r ^ 2))) r) =
      ∫ r in (0 : ℝ)..1, r * (a * b * p₀ * (1 - r ^ 2)) := by
  rw [setIntegral_indicator measurableSet_Iic]
  have hinter :
      Set.Ioi (0 : ℝ) ∩ Set.Iic 1 = Set.Ioc (0 : ℝ) 1 := by
    ext r
    simp [and_comm]
  rw [hinter, intervalIntegral.integral_of_le zero_le_one]

private theorem unitDisk_integral_value (a b p₀ : ℝ) :
    (∫ p in unitDisk, a * b * p₀ * (1 - p.1 ^ 2 - p.2 ^ 2)) =
      Real.pi * a * b * p₀ / 2 := by
  let H : ℝ × ℝ → ℝ :=
    fun p => a * b * p₀ * (1 - p.1 ^ 2 - p.2 ^ 2)
  have hpolar := integral_comp_polarCoord_symm (unitDisk.indicator H)
  rw [integral_indicator unitDisk_measurable] at hpolar
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • unitDisk.indicator H (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic (1 : ℝ)).indicator
              (fun r => r * (a * b * p₀ * (1 - r ^ 2))) r) *
          ∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 • unitDisk.indicator H (polarCoord.symm p)) =
          ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            (Set.Iic (1 : ℝ)).indicator
                (fun r => r * (a * b * p₀ * (1 - r ^ 2))) p.1 *
              (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp
        exact polar_pointwise a b p₀ p hp
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic (1 : ℝ)).indicator
              (fun r => r * (a * b * p₀ * (1 - r ^ 2))) r)
          (fun _ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  rw [hprod, radial_set_integral, angular_integral_one] at hpolar
  rw [← hpolar]
  have hradial :
      (∫ r in (0 : ℝ)..1, r * (a * b * p₀ * (1 - r ^ 2))) =
        a * b * p₀ / 4 := by
    rw [show (fun r : ℝ => r * (a * b * p₀ * (1 - r ^ 2))) =
        fun r => (a * b * p₀) * (r - r ^ 3) by
      funext r
      ring]
    rw [intervalIntegral.integral_const_mul]
    have hc1 : Continuous (fun r : ℝ => r) := continuous_id
    have hc3 : Continuous (fun r : ℝ => r ^ 3) := continuous_id.pow 3
    rw [intervalIntegral.integral_sub
      (hc1.intervalIntegrable (μ := volume) 0 1)
      (hc3.intervalIntegrable (μ := volume) 0 1)]
    rw [integral_id, integral_pow]
    norm_num
    ring
  rw [hradial]
  ring

private theorem averagePressure_value (a b p₀ : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    averagePressure a b p₀ = p₀ / 2 := by
  unfold averagePressure
  rw [ellipse_integral_scaled a b p₀ ha hb,
    unitDisk_integral_value]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [ha.ne', hb.ne', hpi]

theorem gap1 (a b p₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    averagePressure a b p₀ =
      1 / (Real.pi * a * b) *
        ∫ p in ellipse a b,
          p₀ * (1 - p.1 ^ 2 / a ^ 2 - p.2 ^ 2 / b ^ 2) := by
  rfl

theorem gap2 (a b p₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    averagePressure a b p₀ =
      4 / (Real.pi * a * b) *
        (∫ theta in (0 : ℝ)..Real.pi / 2, (1 : ℝ)) *
        ∫ r in (0 : ℝ)..1, p₀ * (1 - r ^ 2) * a * b * r := by
  rw [averagePressure_value a b p₀ ha hb]
  have htheta :
      (∫ theta in (0 : ℝ)..Real.pi / 2, (1 : ℝ)) =
        Real.pi / 2 := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hr :
      (∫ r in (0 : ℝ)..1, p₀ * (1 - r ^ 2) * a * b * r) =
        p₀ * a * b / 4 := by
    rw [show (fun r : ℝ => p₀ * (1 - r ^ 2) * a * b * r) =
        fun r => (p₀ * a * b) * (r - r ^ 3) by
      funext r
      ring]
    rw [intervalIntegral.integral_const_mul]
    have hc1 : Continuous (fun r : ℝ => r) := continuous_id
    have hc3 : Continuous (fun r : ℝ => r ^ 3) := continuous_id.pow 3
    rw [intervalIntegral.integral_sub
      (hc1.intervalIntegrable (μ := volume) 0 1)
      (hc3.intervalIntegrable (μ := volume) 0 1)]
    rw [integral_id, integral_pow]
    norm_num
    ring
  rw [htheta, hr]
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne']

theorem gap3 (a b p₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    averagePressure a b p₀ =
      4 / (Real.pi * a * b) * (Real.pi / 2) *
        (p₀ * a * b / 4) := by
  rw [averagePressure_value a b p₀ ha hb]
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne']

theorem gap4 (a b p₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    averagePressure a b p₀ = p₀ / 2 := by
  exact averagePressure_value a b p₀ ha hb

end

end ProofGap.Exercise4073
