import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3965

noncomputable section

open MeasureTheory
open scoped Interval

local instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

def originalRegion : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ p.1 + p.2}

def centeredRegion : Set (ℝ × ℝ) :=
  {p | (p.1 - 1 / 2) ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 2}

def parameterRegion : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) (1 / Real.sqrt 2) ×ˢ
    Set.Icc (0 : ℝ) (2 * Real.pi)

def shiftedPolar (r φ : ℝ) : ℝ × ℝ :=
  (1 / 2 + r * Real.cos φ, 1 / 2 + r * Real.sin φ)

def jacobianAbs (r : ℝ) : ℝ :=
  |r|

def regionIntegral : ℝ :=
  ∫ p in originalRegion, p.1 + p.2

private def centeredDisk : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1 / 2}

private def centerMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 / 2 + p.1, 1 / 2 + p.2)

private theorem centerMap_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt centerMap (ContinuousLinearMap.id ℝ (ℝ × ℝ)) p := by
  have h :
      HasFDerivAt
        (fun q : ℝ × ℝ => q + ((1 / 2, 1 / 2) : ℝ × ℝ))
        (ContinuousLinearMap.id ℝ (ℝ × ℝ)) p :=
    (hasFDerivAt_id p).add_const ((1 / 2, 1 / 2) : ℝ × ℝ)
  convert h using 1
  funext q
  ext <;> simp [centerMap] <;> ring

private theorem centerMap_image :
    centerMap '' centeredDisk = centeredRegion := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change
      ((centerMap q).1 - 1 / 2) ^ 2 +
          ((centerMap q).2 - 1 / 2) ^ 2 ≤ 1 / 2
    change q.1 ^ 2 + q.2 ^ 2 ≤ 1 / 2 at hq
    simpa [centerMap] using hq
  · intro hp
    let q : ℝ × ℝ := (p.1 - 1 / 2, p.2 - 1 / 2)
    have hq : q ∈ centeredDisk := by
      change
        (p.1 - 1 / 2) ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 2
      exact hp
    refine ⟨q, hq, ?_⟩
    ext <;> simp [q, centerMap]

private theorem centerMap_injective :
    Set.InjOn centerMap centeredDisk := by
  intro p hp q hq h
  ext
  · have h' := congrArg Prod.fst h
    simpa [centerMap] using h'
  · have h' := congrArg Prod.snd h
    simpa [centerMap] using h'

private theorem centered_integral :
    regionIntegral =
      ∫ p in centeredDisk, 1 + p.1 + p.2 := by
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (s := centeredDisk)
      (by
        exact isClosed_le
          ((continuous_fst.pow 2).add (continuous_snd.pow 2))
          continuous_const |>.measurableSet)
      (fun p _ => (centerMap_hasFDerivAt p).hasFDerivWithinAt)
      centerMap_injective
      (fun p : ℝ × ℝ => p.1 + p.2)
  rw [centerMap_image] at hchange
  calc
    regionIntegral =
        ∫ p in centeredRegion, p.1 + p.2 := by
      unfold regionIntegral
      rw [show originalRegion = centeredRegion by
        ext p
        simp only [originalRegion, centeredRegion, Set.mem_setOf_eq]
        constructor <;> intro h <;> nlinarith]
    _ =
        ∫ p in centeredDisk,
          |(ContinuousLinearMap.id ℝ (ℝ × ℝ)).det| •
            ((centerMap p).1 + (centerMap p).2) := hchange
    _ = ∫ p in centeredDisk, 1 + p.1 + p.2 := by
      apply setIntegral_congr_fun
        (isClosed_le
          ((continuous_fst.pow 2).add (continuous_snd.pow 2))
          continuous_const |>.measurableSet)
      intro p hp
      have hid_det :
          (ContinuousLinearMap.id ℝ (ℝ × ℝ)).det = 1 := by
        rw [ContinuousLinearMap.det]
        change
          LinearMap.det
            (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = 1
        exact LinearMap.det_id
      rw [hid_det]
      simp only [abs_one, one_smul, centerMap]
      ring

private theorem polar_integral :
    (∫ p in centeredDisk, 1 + p.1 + p.2) =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1 / Real.sqrt 2,
          r + r ^ 2 * (Real.sin phi + Real.cos phi) := by
  let R : ℝ := 1 / Real.sqrt 2
  let g : ℝ × ℝ → ℝ := fun p => 1 + p.1 + p.2
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi
  let radial : ℝ × ℝ → ℝ := fun p =>
    p.1 + p.1 ^ 2 * (Real.sin p.2 + Real.cos p.2)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRsq : R ^ 2 = (1 / 2 : ℝ) := by
    dsimp [R]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp [hsqrt_pos.ne']
    nlinarith
  have hrect_meas : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hrect_sub :
      rect ⊆ Set.Icc (0 : ℝ) R ×ˢ
        Set.Icc (-Real.pi) Real.pi := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hradial_cont : Continuous radial := by
    dsimp [radial]
    fun_prop
  have hrect_integrable : Integrable (rect.indicator radial) := by
    rw [integrable_indicator_iff hrect_meas]
    exact
      (hradial_cont.continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set hrect_sub
  have hpolar_point (p : ℝ × ℝ) :
      polarCoord.target.indicator
          (fun q => q.1 * centeredDisk.indicator g (polarCoord.symm q)) p =
        rect.indicator radial p := by
    by_cases ht : p ∈ polarCoord.target
    · have hrpos : 0 < p.1 := ht.1
      have hang : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := ht.2
      have hnorm :
          (polarCoord.symm p).1 ^ 2 +
              (polarCoord.symm p).2 ^ 2 =
            p.1 ^ 2 := by
        simp only [polarCoord_symm_apply]
        rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
      by_cases hrR : p.1 ≤ R
      · have hd : polarCoord.symm p ∈ centeredDisk := by
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ 1 / 2
          rw [hnorm, ← hRsq]
          nlinarith
        have hp_rect : p ∈ rect := ⟨⟨hrpos, hrR⟩, hang⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem hp_rect,
          Set.indicator_of_mem hd]
        simp only [g, radial, polarCoord_symm_apply]
        ring
      · have hd : polarCoord.symm p ∉ centeredDisk := by
          intro hd
          apply hrR
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ 1 / 2 at hd
          rw [hnorm, ← hRsq] at hd
          nlinarith
        have hp_rect : p ∉ rect := fun hp => hrR hp.1.2
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hd,
          Set.indicator_of_notMem hp_rect]
        simp
    · have hp_rect : p ∉ rect := by
        intro hp
        apply ht
        exact ⟨hp.1.1, hp.2⟩
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hp_rect]
  have hpolar :
      (∫ p in centeredDisk, 1 + p.1 + p.2) =
        ∫ p : ℝ × ℝ, rect.indicator radial p := by
    have hp := integral_comp_polarCoord_symm (centeredDisk.indicator g)
    calc
      (∫ p in centeredDisk, 1 + p.1 + p.2) =
          ∫ p : ℝ × ℝ, centeredDisk.indicator g p := by
        change
          (∫ p in centeredDisk, g p) =
            ∫ p : ℝ × ℝ, centeredDisk.indicator g p
        symm
        exact integral_indicator
          (isClosed_le
            ((continuous_fst.pow 2).add (continuous_snd.pow 2))
            continuous_const |>.measurableSet)
      _ =
          ∫ p in polarCoord.target,
            p.1 * centeredDisk.indicator g (polarCoord.symm p) := by
        simpa only [smul_eq_mul] using hp.symm
      _ =
          ∫ p : ℝ × ℝ, rect.indicator radial p := by
        rw [← integral_indicator polarCoord.open_target.measurableSet]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with p
        exact hpolar_point p
  have hrect_on : IntegrableOn radial rect :=
    (integrable_indicator_iff hrect_meas).mp hrect_integrable
  have hrect_eval :
      (∫ p : ℝ × ℝ, rect.indicator radial p) =
        ∫ phi in -Real.pi..Real.pi,
          ∫ r in (0 : ℝ)..R,
            r + r ^ 2 * (Real.sin phi + Real.cos phi) := by
    calc
      (∫ p : ℝ × ℝ, rect.indicator radial p) =
          ∫ p in rect, radial p := by
        rw [integral_indicator hrect_meas]
      _ =
          ∫ q in Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioc (0 : ℝ) R,
            (radial ∘ Prod.swap) q := by
        exact
          (MeasureTheory.setIntegral_prod_swap
            (Set.Ioc (0 : ℝ) R) (Set.Ioo (-Real.pi) Real.pi) radial).symm
      _ =
          ∫ phi in Set.Ioo (-Real.pi) Real.pi,
            ∫ r in Set.Ioc (0 : ℝ) R, radial (r, phi) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.setIntegral_prod
            (μ := volume) (ν := volume)
            (radial ∘ Prod.swap) hrect_on.swap)
      _ =
          ∫ phi in -Real.pi..Real.pi,
            ∫ r in (0 : ℝ)..R,
              r + r ^ 2 * (Real.sin phi + Real.cos phi) := by
        rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
        rw [← intervalIntegral.integral_of_le
          (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
        apply intervalIntegral.integral_congr
        intro phi hphi
        change
          (∫ r in Set.Ioc (0 : ℝ) R, radial (r, phi)) =
            ∫ r in (0 : ℝ)..R,
              r + r ^ 2 * (Real.sin phi + Real.cos phi)
        rw [← intervalIntegral.integral_of_le hRpos.le]
  let H : ℝ → ℝ := fun phi =>
    ∫ r in (0 : ℝ)..R,
      r + r ^ 2 * (Real.sin phi + Real.cos phi)
  have hperiod : Function.Periodic H (2 * Real.pi) := by
    intro phi
    dsimp only [H]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hshift :
      (∫ phi in -Real.pi..Real.pi, H phi) =
        ∫ phi in (0 : ℝ)..2 * Real.pi, H phi := by
    have h := hperiod.intervalIntegral_add_eq (-Real.pi) 0
    convert h using 1 <;> ring
  rw [hpolar, hrect_eval]
  change (∫ phi in -Real.pi..Real.pi, H phi) = _
  rw [hshift]

private theorem parameter_integral_eval :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1 / Real.sqrt 2,
          r + r ^ 2 * (Real.sin phi + Real.cos phi)) =
      Real.pi / 2 := by
  let R : ℝ := 1 / Real.sqrt 2
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hRsq : R ^ 2 = (1 / 2 : ℝ) := by
    dsimp [R]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp [hsqrt_pos.ne']
    nlinarith
  have hinner (phi : ℝ) :
      (∫ r in (0 : ℝ)..R,
          r + r ^ 2 * (Real.sin phi + Real.cos phi)) =
        R ^ 2 / 2 +
          R ^ 3 / 3 * (Real.sin phi + Real.cos phi) := by
    have hid :
        IntervalIntegrable (fun r : ℝ => r) volume 0 R :=
      continuous_id.intervalIntegrable _ _
    have hpow :
        IntervalIntegrable
          (fun r : ℝ => r ^ 2 * (Real.sin phi + Real.cos phi))
          volume 0 R :=
      ((continuous_id.pow 2).mul continuous_const).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hid hpow]
    rw [integral_id]
    rw [show
      (fun r : ℝ => r ^ 2 * (Real.sin phi + Real.cos phi)) =
        fun r => (Real.sin phi + Real.cos phi) * r ^ 2 by
          funext r
          ring]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  change
    (∫ phi in (0 : ℝ)..2 * Real.pi,
      ∫ r in (0 : ℝ)..R,
        r + r ^ 2 * (Real.sin phi + Real.cos phi)) = _
  simp_rw [hinner]
  have hconst :
      IntervalIntegrable (fun _phi : ℝ => R ^ 2 / 2)
        volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have htrig :
      IntervalIntegrable
        (fun phi : ℝ =>
          R ^ 3 / 3 * (Real.sin phi + Real.cos phi))
        volume 0 (2 * Real.pi) :=
    (continuous_const.mul
      (Real.continuous_sin.add Real.continuous_cos)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hconst htrig]
  rw [intervalIntegral.integral_const]
  rw [show
    (fun phi : ℝ =>
      R ^ 3 / 3 * (Real.sin phi + Real.cos phi)) =
      fun phi =>
        R ^ 3 / 3 * Real.sin phi + R ^ 3 / 3 * Real.cos phi by
          funext phi
          ring]
  have hsin :
      IntervalIntegrable (fun phi : ℝ => R ^ 3 / 3 * Real.sin phi)
        volume 0 (2 * Real.pi) :=
    (continuous_const.mul Real.continuous_sin).intervalIntegrable _ _
  have hcos :
      IntervalIntegrable (fun phi : ℝ => R ^ 3 / 3 * Real.cos phi)
        volume 0 (2 * Real.pi) :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hsin hcos]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  simp
  rw [hRsq]
  ring

theorem gap1 :
    originalRegion = centeredRegion := by
  ext p
  simp only [originalRegion, centeredRegion, Set.mem_setOf_eq]
  constructor <;> intro h <;> nlinarith

theorem gap2 :
    parameterRegion =
      {p | 0 ≤ p.2 ∧ p.2 ≤ 2 * Real.pi ∧
        0 ≤ p.1 ∧ p.1 ≤ 1 / Real.sqrt 2} := by
  ext p
  simp only [parameterRegion, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq]
  aesop

theorem gap3 (r : ℝ) (hr : 0 ≤ r) :
    jacobianAbs r = r := by
  exact abs_of_nonneg hr

theorem gap4 :
    regionIntegral =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1 / Real.sqrt 2,
          r + r ^ 2 * (Real.sin φ + Real.cos φ) := by
  rw [centered_integral, polar_integral]

theorem gap5 :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1 / Real.sqrt 2,
          r + r ^ 2 * (Real.sin φ + Real.cos φ)) =
      Real.pi / 2 := by
  exact parameter_integral_eval

theorem gap6 :
    regionIntegral = Real.pi / 2 := by
  rw [gap4, gap5]

end

end ProofGap.Exercise3965
