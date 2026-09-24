import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3967

noncomputable section

open MeasureTheory
open scoped Interval

local instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

def ellipse (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤ 1}

def parameterRegion : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)

def ellipseMap (a b r φ : ℝ) : ℝ × ℝ :=
  (a * r * Real.cos φ, b * r * Real.sin φ)

def jacobianAbs (a b r : ℝ) : ℝ :=
  |a * b * r|

def ellipseIntegral (a b : ℝ) : ℝ :=
  ∫ p in ellipse a b,
    Real.sqrt (1 - p.1 ^ 2 / a ^ 2 - p.2 ^ 2 / b ^ 2)

private def unitDisk : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

private def scaleMap (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (a * p.1, b * p.2)

private def scaleDerivative (a b : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![a, 0; 0, b]).toContinuousLinearMap

private theorem scaleMap_hasFDerivAt (a b : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (scaleMap a b) (scaleDerivative a b) p := by
  have hfst :
      HasFDerivAt (fun q : ℝ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hsnd :
      HasFDerivAt (fun q : ℝ × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  unfold scaleMap scaleDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert HasFDerivAt.prodMk
    (hfst.const_smul a)
    (hsnd.const_smul b) using 1 <;>
    ext <;> simp

private theorem scaleDerivative_det (a b : ℝ) :
    (scaleDerivative a b).det = a * b := by
  unfold scaleDerivative
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

private theorem scaleMap_image (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    scaleMap a b '' unitDisk = ellipse a b := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change
      (a * q.1) ^ 2 / a ^ 2 +
          (b * q.2) ^ 2 / b ^ 2 ≤ 1
    change q.1 ^ 2 + q.2 ^ 2 ≤ 1 at hq
    have hx : (a * q.1) ^ 2 / a ^ 2 = q.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * q.2) ^ 2 / b ^ 2 = q.2 ^ 2 := by
      field_simp [hb.ne']
    rwa [hx, hy]
  · intro hp
    let q : ℝ × ℝ := (p.1 / a, p.2 / b)
    have hq : q ∈ unitDisk := by
      change (p.1 / a) ^ 2 + (p.2 / b) ^ 2 ≤ 1
      change p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤ 1 at hp
      convert hp using 1 <;> ring
    refine ⟨q, hq, ?_⟩
    ext
    · dsimp [q, scaleMap]
      field_simp [ha.ne']
    · dsimp [q, scaleMap]
      field_simp [hb.ne']

private theorem scaleMap_injective (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Set.InjOn (scaleMap a b) unitDisk := by
  intro p hp q hq h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [scaleMap] at hx hy
  ext
  · apply (mul_left_cancel₀ ha.ne')
    exact hx
  · apply (mul_left_cancel₀ hb.ne')
    exact hy

private theorem ellipseIntegral_eq_unitDisk
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipseIntegral a b =
      ∫ q in unitDisk,
        a * b * Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2) := by
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (s := unitDisk)
      (isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const |>.measurableSet)
      (fun q _ => (scaleMap_hasFDerivAt a b q).hasFDerivWithinAt)
      (scaleMap_injective a b ha hb)
      (fun p : ℝ × ℝ =>
        Real.sqrt (1 - p.1 ^ 2 / a ^ 2 - p.2 ^ 2 / b ^ 2))
  rw [scaleMap_image a b ha hb] at hchange
  calc
    ellipseIntegral a b =
        ∫ q in unitDisk,
          |(scaleDerivative a b).det| •
            Real.sqrt
              (1 - (scaleMap a b q).1 ^ 2 / a ^ 2 -
                (scaleMap a b q).2 ^ 2 / b ^ 2) := hchange
    _ =
        ∫ q in unitDisk,
          a * b * Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2) := by
      apply setIntegral_congr_fun
        (isClosed_le
          ((continuous_fst.pow 2).add (continuous_snd.pow 2))
          continuous_const |>.measurableSet)
      intro q hq
      rw [scaleDerivative_det, abs_of_pos (mul_pos ha hb)]
      simp only [scaleMap, smul_eq_mul]
      have hx : (a * q.1) ^ 2 / a ^ 2 = q.1 ^ 2 := by
        field_simp [ha.ne']
      have hy : (b * q.2) ^ 2 / b ^ 2 = q.2 ^ 2 := by
        field_simp [hb.ne']
      rw [hx, hy]

private theorem unitDisk_polar
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ q in unitDisk,
        a * b * Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2)) =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..1,
          a * b * Real.sqrt (1 - r ^ 2) * r := by
  let g : ℝ × ℝ → ℝ := fun q =>
    a * b * Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2)
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi
  let radial : ℝ × ℝ → ℝ := fun p =>
    a * b * Real.sqrt (1 - p.1 ^ 2) * p.1
  have hrect_meas : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hrect_sub :
      rect ⊆ Set.Icc (0 : ℝ) 1 ×ˢ
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
          (fun q => q.1 * unitDisk.indicator g (polarCoord.symm q)) p =
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
      have hgpolar :
          g (polarCoord.symm p) =
            a * b * Real.sqrt (1 - p.1 ^ 2) := by
        dsimp only [g]
        congr 2
        linarith
      by_cases hr1 : p.1 ≤ 1
      · have hd : polarCoord.symm p ∈ unitDisk := by
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ 1
          rw [hnorm]
          nlinarith
        have hp_rect : p ∈ rect := ⟨⟨hrpos, hr1⟩, hang⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem hp_rect,
          Set.indicator_of_mem hd, hgpolar]
        dsimp [radial]
        ring
      · have hd : polarCoord.symm p ∉ unitDisk := by
          intro hd
          apply hr1
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ 1 at hd
          rw [hnorm] at hd
          nlinarith
        have hp_rect : p ∉ rect := fun hp => hr1 hp.1.2
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hd,
          Set.indicator_of_notMem hp_rect]
        simp
    · have hp_rect : p ∉ rect := by
        intro hp
        apply ht
        exact ⟨hp.1.1, hp.2⟩
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hp_rect]
  have hpolar :
      (∫ q in unitDisk,
          a * b * Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2)) =
        ∫ p : ℝ × ℝ, rect.indicator radial p := by
    have hp := integral_comp_polarCoord_symm (unitDisk.indicator g)
    calc
      (∫ q in unitDisk,
          a * b * Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2)) =
          ∫ q : ℝ × ℝ, unitDisk.indicator g q := by
        change
          (∫ q in unitDisk, g q) =
            ∫ q : ℝ × ℝ, unitDisk.indicator g q
        symm
        exact integral_indicator
          (isClosed_le
            ((continuous_fst.pow 2).add (continuous_snd.pow 2))
            continuous_const |>.measurableSet)
      _ =
          ∫ p in polarCoord.target,
            p.1 * unitDisk.indicator g (polarCoord.symm p) := by
        simpa only [smul_eq_mul] using hp.symm
      _ =
          ∫ p : ℝ × ℝ, rect.indicator radial p := by
        rw [← integral_indicator polarCoord.open_target.measurableSet]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with p
        exact hpolar_point p
  have hrect_eval :
      (∫ p : ℝ × ℝ, rect.indicator radial p) =
        2 * Real.pi *
          ∫ r in (0 : ℝ)..1,
            a * b * Real.sqrt (1 - r ^ 2) * r := by
    change
      (∫ p : ℝ × ℝ, rect.indicator radial p
        ∂((volume : Measure ℝ).prod volume)) = _
    change Integrable (rect.indicator radial)
      ((volume : Measure ℝ).prod volume) at hrect_integrable
    rw [integral_prod _ hrect_integrable]
    have hsection (r : ℝ) :
        (∫ phi : ℝ, rect.indicator radial (r, phi)) =
          (Set.Ioc (0 : ℝ) 1).indicator
            (fun r =>
              2 * Real.pi *
                (a * b * Real.sqrt (1 - r ^ 2) * r)) r := by
      by_cases hr : r ∈ Set.Ioc (0 : ℝ) 1
      · rw [Set.indicator_of_mem hr]
        calc
          (∫ phi : ℝ, rect.indicator radial (r, phi)) =
              ∫ _phi in Set.Ioo (-Real.pi) Real.pi,
                a * b * Real.sqrt (1 - r ^ 2) * r := by
            rw [← integral_indicator measurableSet_Ioo]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with phi
            by_cases hphi : phi ∈ Set.Ioo (-Real.pi) Real.pi
            · simp [rect, radial, hr, hphi]
            · simp [rect, radial, hr, hphi]
          _ =
              2 * Real.pi *
                (a * b * Real.sqrt (1 - r ^ 2) * r) := by
            rw [MeasureTheory.setIntegral_const]
            have hvol :
                (volume : Measure ℝ).real
                    (Set.Ioo (-Real.pi) Real.pi) =
                  2 * Real.pi := by
              simp [Measure.real, Real.volume_Ioo, Real.pi_pos.le]
              ring
            rw [hvol]
            simp [smul_eq_mul]
      · have hz :
          (fun phi : ℝ => rect.indicator radial (r, phi)) = 0 := by
          funext phi
          simp [rect, hr]
        rw [hz]
        simp [hr]
    simp_rw [hsection]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul]
  exact hpolar.trans hrect_eval

private theorem ellipseIntegral_eq_radial
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipseIntegral a b =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..1,
          a * b * Real.sqrt (1 - r ^ 2) * r := by
  rw [ellipseIntegral_eq_unitDisk a b ha hb,
    unitDisk_polar a b ha hb]

private theorem radial_integral_eval :
    (∫ r in (0 : ℝ)..1, Real.sqrt (1 - r ^ 2) * r) =
      1 / 3 := by
  let F : ℝ → ℝ :=
    fun r => (r ^ 2 - 1) * Real.sqrt (1 - r ^ 2) / 3
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    exact (by fun_prop : Continuous F).continuousOn
  have hd :
      ∀ r ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt F (Real.sqrt (1 - r ^ 2) * r) r := by
    intro r hr
    have hpos : 0 < 1 - r ^ 2 := by
      nlinarith [sq_lt_sq₀ hr.1.le (by norm_num : (0 : ℝ) ≤ 1) |>.2 hr.2]
    have hinner :
        HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2)
        using 1 <;> simp only [id_eq] <;> ring
    have hfirst :
        HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * r) r := by
      convert ((hasDerivAt_id r).pow 2).sub_const 1 using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt :
        HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
          (1 / (2 * Real.sqrt (1 - r ^ 2)) * (-2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hpos.ne').comp r hinner
    have hsquare :
        Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
      Real.sq_sqrt hpos.le
    dsimp [F]
    convert ((hfirst.mul hsqrt).div_const 3) using 1
    field_simp [Real.sqrt_ne_zero'.mpr hpos]
    rw [hsquare]
    ring
  have hi :
      IntervalIntegrable
        (fun r : ℝ => Real.sqrt (1 - r ^ 2) * r)
        volume 0 1 :=
    (by fun_prop : Continuous
      (fun r : ℝ => Real.sqrt (1 - r ^ 2) * r)).intervalIntegrable _ _
  have hFTC :
      (∫ r in (0 : ℝ)..1, Real.sqrt (1 - r ^ 2) * r) =
        F 1 - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      zero_le_one hcont hd hi
  convert hFTC using 1 <;> norm_num [F]

theorem gap1 :
    parameterRegion =
      {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
        0 ≤ p.2 ∧ p.2 ≤ 2 * Real.pi} := by
  ext p
  simp only [parameterRegion, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨h₁, h₂, h₃, h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩

theorem gap2 (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ r) :
    jacobianAbs a b r = a * b * r := by
  exact abs_of_nonneg (mul_nonneg (mul_nonneg ha.le hb.le) hr)

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipseIntegral a b =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          a * b * Real.sqrt (1 - r ^ 2) * r := by
  rw [ellipseIntegral_eq_radial a b ha hb]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          a * b * Real.sqrt (1 - r ^ 2) * r) =
      2 * Real.pi * a * b *
        ∫ r in (0 : ℝ)..1, Real.sqrt (1 - r ^ 2) * r := by
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  have hinner :
      (∫ r in (0 : ℝ)..1,
          a * b * Real.sqrt (1 - r ^ 2) * r) =
        a * b *
          ∫ r in (0 : ℝ)..1, Real.sqrt (1 - r ^ 2) * r := by
    rw [show
      (fun r : ℝ => a * b * Real.sqrt (1 - r ^ 2) * r) =
        fun r => (a * b) * (Real.sqrt (1 - r ^ 2) * r) by
          funext r
          ring]
    rw [intervalIntegral.integral_const_mul]
  rw [hinner]
  ring

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * Real.pi * a * b *
        (∫ r in (0 : ℝ)..1, Real.sqrt (1 - r ^ 2) * r) =
      2 * Real.pi * a * b / 3 := by
  rw [radial_integral_eval]
  ring

theorem gap6 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipseIntegral a b = 2 * Real.pi * a * b / 3 := by
  rw [gap3 a b ha hb, gap4 a b ha hb, gap5 a b ha hb]

end

end ProofGap.Exercise3967
