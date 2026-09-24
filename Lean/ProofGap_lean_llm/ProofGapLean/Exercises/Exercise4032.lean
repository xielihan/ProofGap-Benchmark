import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4032

noncomputable section

open MeasureTheory
open scoped Interval

def superellipseGauge (a b x y : ℝ) : ℝ :=
  Real.rpow |x / a| (2 / 3 : ℝ) +
    Real.rpow |y / b| (2 / 3 : ℝ)

def baseRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | superellipseGauge a b p.1 p.2 ≤ 1}

def paramX (a r φ : ℝ) : ℝ :=
  a * r * Real.cos φ ^ 3

def paramY (b r φ : ℝ) : ℝ :=
  b * r * Real.sin φ ^ 3

def radialHeight (c r φ : ℝ) : ℝ :=
  c * (1 - r ^ 2 * (Real.cos φ ^ 6 + Real.sin φ ^ 6))

def parameterDomain : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)

def volume (a b c : ℝ) : ℝ :=
  ∫ p in baseRegion a b,
    c * (1 - (p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2))

private theorem abs_cube_rpow_two_thirds (z : ℝ) :
    Real.rpow |z ^ 3| (2 / 3 : ℝ) = z ^ 2 := by
  rw [abs_pow]
  have hz : 0 ≤ |z| := abs_nonneg z
  calc
    Real.rpow (|z| ^ 3) (2 / 3 : ℝ) =
        Real.rpow (Real.rpow |z| (3 : ℝ)) (2 / 3 : ℝ) := by
      congr 1
      exact (Real.rpow_natCast |z| 3).symm
    _ = Real.rpow |z| ((3 : ℝ) * (2 / 3 : ℝ)) :=
      (Real.rpow_mul hz 3 (2 / 3 : ℝ)).symm
    _ = Real.rpow |z| (2 : ℝ) := by norm_num
    _ = |z| ^ 2 := Real.rpow_natCast |z| 2
    _ = z ^ 2 := sq_abs z

private theorem abs_mul_cube_rpow_two_thirds
    (r z : ℝ) (hr : 0 ≤ r) :
    Real.rpow |r * z ^ 3| (2 / 3 : ℝ) =
      Real.rpow r (2 / 3 : ℝ) * z ^ 2 := by
  rw [abs_mul, abs_of_nonneg hr]
  calc
    Real.rpow (r * |z ^ 3|) (2 / 3 : ℝ) =
        Real.rpow r (2 / 3 : ℝ) *
          Real.rpow |z ^ 3| (2 / 3 : ℝ) :=
      Real.mul_rpow hr (abs_nonneg (z ^ 3))
    _ = Real.rpow r (2 / 3 : ℝ) * z ^ 2 := by
      rw [abs_cube_rpow_two_thirds]

theorem gap1 (c r φ : ℝ) :
    radialHeight c r φ =
      c * (1 - r ^ 2 * (Real.cos φ ^ 6 + Real.sin φ ^ 6)) := by
  rfl

theorem gap2 (a b r φ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ r)
    (hboundary :
      superellipseGauge a b (paramX a r φ) (paramY b r φ) = 1) :
    r = 1 := by
  have hx :
      paramX a r φ / a = r * Real.cos φ ^ 3 := by
    dsimp [paramX]
    field_simp [ha.ne']
  have hy :
      paramY b r φ / b = r * Real.sin φ ^ 3 := by
    dsimp [paramY]
    field_simp [hb.ne']
  rw [superellipseGauge, hx, hy,
    abs_mul_cube_rpow_two_thirds r (Real.cos φ) hr,
    abs_mul_cube_rpow_two_thirds r (Real.sin φ) hr,
    ← mul_add, Real.cos_sq_add_sin_sq, mul_one] at hboundary
  have hpow :
      Real.rpow r (2 / 3 : ℝ) =
        Real.rpow 1 (2 / 3 : ℝ) := by
    simpa using hboundary
  have hle : r ≤ 1 :=
    (Real.rpow_le_rpow_iff hr zero_le_one (by norm_num)).1 hpow.le
  have hge : 1 ≤ r :=
    (Real.rpow_le_rpow_iff zero_le_one hr (by norm_num)).1 hpow.ge
  exact le_antisymm hle hge

theorem gap3 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    0 ≤ φ := by
  exact hp.2.1

theorem gap4 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    φ ≤ 2 * Real.pi := by
  exact hp.2.2

theorem gap5 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    0 ≤ r := by
  exact hp.1.1

theorem gap6 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    r ≤ 1 := by
  exact hp.1.2

private def unitDisk : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

private def cubeRoot (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.rpow x (1 / 3 : ℝ)
  else -Real.rpow (-x) (1 / 3 : ℝ)

private theorem cubeRoot_cube (x : ℝ) :
    cubeRoot x ^ 3 = x := by
  unfold cubeRoot
  split_ifs with hx
  · simpa [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num] using
      (Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0))
  · have hnx : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
    have hroot :=
      Real.rpow_inv_natCast_pow hnx (by norm_num : (3 : ℕ) ≠ 0)
    rw [(show Odd 3 by decide).neg_pow]
    norm_num [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num] at hroot ⊢
    linarith

private theorem cubeRoot_sq (x : ℝ) :
    cubeRoot x ^ 2 = Real.rpow |x| (2 / 3 : ℝ) := by
  unfold cubeRoot
  split_ifs with hx
  · rw [abs_of_nonneg hx]
    calc
      Real.rpow x (1 / 3 : ℝ) ^ 2 =
          Real.rpow (x ^ 2) (1 / 3 : ℝ) :=
        Real.rpow_pow_comm hx (1 / 3 : ℝ) 2
      _ = Real.rpow x ((2 : ℝ) * (1 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul hx 2 (1 / 3 : ℝ)).symm
      _ = Real.rpow x (2 / 3 : ℝ) := by norm_num
  · have hnx : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
    rw [abs_of_neg (lt_of_not_ge hx)]
    rw [show (-Real.rpow (-x) (1 / 3 : ℝ)) ^ 2 =
      Real.rpow (-x) (1 / 3 : ℝ) ^ 2 by ring]
    calc
      Real.rpow (-x) (1 / 3 : ℝ) ^ 2 =
          Real.rpow ((-x) ^ 2) (1 / 3 : ℝ) :=
        Real.rpow_pow_comm hnx (1 / 3 : ℝ) 2
      _ = Real.rpow (-x) ((2 : ℝ) * (1 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul hnx 2 (1 / 3 : ℝ)).symm
      _ = Real.rpow (-x) (2 / 3 : ℝ) := by norm_num

private def cubeMap (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (a * p.1 ^ 3, b * p.2 ^ 3)

private def scale1 (d : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ d

private def cubeDeriv (a b : ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (scale1 (3 * a * p.1 ^ 2)).prodMap
    (scale1 (3 * b * p.2 ^ 2))

@[simp] private theorem scale1_apply (d x : ℝ) :
    scale1 d x = d * x := by
  simp [scale1]
  ring

private theorem det_scale1 (d : ℝ) :
    (scale1 d).det = d := by
  rw [ContinuousLinearMap.det, LinearMap.det_ring]
  simp [scale1]

private theorem det_cubeDeriv (a b : ℝ) (p : ℝ × ℝ) :
    (cubeDeriv a b p).det =
      9 * a * b * p.1 ^ 2 * p.2 ^ 2 := by
  unfold cubeDeriv
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap,
    LinearMap.det_prodMap]
  change
    (scale1 (3 * a * p.1 ^ 2)).det *
      (scale1 (3 * b * p.2 ^ 2)).det = _
  rw [det_scale1, det_scale1]
  ring

private theorem cubeMap_hasFDerivAt (a b : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (cubeMap a b) (cubeDeriv a b p) p := by
  have hx :
      HasDerivAt (fun x : ℝ => a * x ^ 3)
        (3 * a * p.1 ^ 2) p.1 := by
    convert
      (hasDerivAt_const p.1 a).mul ((hasDerivAt_id p.1).pow 3)
      using 1 <;> simp <;> ring
  have hy :
      HasDerivAt (fun y : ℝ => b * y ^ 3)
        (3 * b * p.2 ^ 2) p.2 := by
    convert
      (hasDerivAt_const p.2 b).mul ((hasDerivAt_id p.2).pow 3)
      using 1 <;> simp <;> ring
  simpa [cubeMap, cubeDeriv, scale1] using
    hx.hasFDerivAt.prodMap p hy.hasFDerivAt

private theorem cubeMap_image_unitDisk (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    cubeMap a b '' unitDisk = baseRegion a b := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hx : a * p.1 ^ 3 / a = p.1 ^ 3 := by
      field_simp [ha.ne']
    have hy : b * p.2 ^ 3 / b = p.2 ^ 3 := by
      field_simp [hb.ne']
    change
      superellipseGauge a b
        (cubeMap a b p).1 (cubeMap a b p).2 ≤ 1
    rw [superellipseGauge]
    change
      Real.rpow |a * p.1 ^ 3 / a| (2 / 3 : ℝ) +
        Real.rpow |b * p.2 ^ 3 / b| (2 / 3 : ℝ) ≤ 1
    rw [hx, hy, abs_cube_rpow_two_thirds,
      abs_cube_rpow_two_thirds]
    exact hp
  · intro hq
    let p : ℝ × ℝ :=
      (cubeRoot (q.1 / a), cubeRoot (q.2 / b))
    have hmap : cubeMap a b p = q := by
      apply Prod.ext
      · dsimp [cubeMap, p]
        rw [cubeRoot_cube]
        field_simp [ha.ne']
      · dsimp [cubeMap, p]
        rw [cubeRoot_cube]
        field_simp [hb.ne']
    refine ⟨p, ?_, hmap⟩
    change p.1 ^ 2 + p.2 ^ 2 ≤ 1
    dsimp [p]
    rw [cubeRoot_sq, cubeRoot_sq]
    simpa [baseRegion, superellipseGauge] using hq

private theorem cubeMap_injOn (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    Set.InjOn (cubeMap a b) unitDisk := by
  intro p hp q hq heq
  have hx : p.1 ^ 3 = q.1 ^ 3 := by
    have h := congrArg Prod.fst heq
    simp only [cubeMap] at h
    exact mul_left_cancel₀ ha.ne' h
  have hy : p.2 ^ 3 = q.2 ^ 3 := by
    have h := congrArg Prod.snd heq
    simp only [cubeMap] at h
    exact mul_left_cancel₀ hb.ne' h
  exact Prod.ext ((show Odd 3 by decide).pow_injective hx)
    ((show Odd 3 by decide).pow_injective hy)

private theorem unitDisk_closed : IsClosed unitDisk := by
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem cube_change_variables
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (g : ℝ × ℝ → ℝ) :
    (∫ q in baseRegion a b, g q) =
      ∫ p in unitDisk,
        (9 * a * b * p.1 ^ 2 * p.2 ^ 2) *
          g (cubeMap a b p) := by
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) unitDisk_closed.measurableSet
      (f := cubeMap a b) (f' := cubeDeriv a b)
      (fun p hp =>
        (cubeMap_hasFDerivAt a b p).hasFDerivWithinAt)
      (cubeMap_injOn a b ha hb) g
  rw [cubeMap_image_unitDisk a b ha hb] at hchange
  have hnonneg (p : ℝ × ℝ) :
      0 ≤ 9 * a * b * p.1 ^ 2 * p.2 ^ 2 := by positivity
  simpa only [det_cubeDeriv, abs_of_nonneg (hnonneg _),
    smul_eq_mul] using hchange

private theorem unitDisk_compact : IsCompact unitDisk := by
  have hsub :
      unitDisk ⊆
        Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro p hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ 1 at hp
    constructor <;> constructor <;>
      nlinarith [sq_nonneg (p.1 + 1), sq_nonneg (p.1 - 1),
        sq_nonneg (p.2 + 1), sq_nonneg (p.2 - 1)]
  exact
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      unitDisk_closed hsub

private theorem unitDisk_polar
    (H : ℝ × ℝ → ℝ) (hH : Continuous H) :
    (∫ p in unitDisk, H p) =
      ∫ φ in -Real.pi..Real.pi,
        ∫ r in (0 : ℝ)..1,
          r * H (r * Real.cos φ, r * Real.sin φ) := by
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi
  let radial : ℝ × ℝ → ℝ :=
    fun p =>
      p.1 *
        H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  have hrect_meas : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hrect_sub :
      rect ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ
          Set.Icc (-Real.pi) Real.pi := by
    intro p hp
    exact
      ⟨⟨hp.1.1.le, hp.1.2⟩,
        ⟨hp.2.1.le, hp.2.2.le⟩⟩
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
          (fun q =>
            q.1 *
              unitDisk.indicator H (polarCoord.symm q)) p =
        rect.indicator radial p := by
    by_cases ht : p ∈ polarCoord.target
    · have hrpos : 0 < p.1 := ht.1
      have hang : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := ht.2
      have hnorm :
          (polarCoord.symm p).1 ^ 2 +
              (polarCoord.symm p).2 ^ 2 =
            p.1 ^ 2 := by
        simp only [polarCoord_symm_apply]
        rw [mul_pow, mul_pow, ← mul_add,
          Real.cos_sq_add_sin_sq, mul_one]
      by_cases hr : p.1 ≤ 1
      · have hd : polarCoord.symm p ∈ unitDisk := by
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ 1
          rw [hnorm]
          nlinarith
        have hp_rect : p ∈ rect := ⟨⟨hrpos, hr⟩, hang⟩
        rw [Set.indicator_of_mem ht,
          Set.indicator_of_mem hp_rect,
          Set.indicator_of_mem hd]
        rfl
      · have hd : polarCoord.symm p ∉ unitDisk := by
          intro hd
          apply hr
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ 1 at hd
          rw [hnorm] at hd
          nlinarith
        have hp_rect : p ∉ rect := fun hp => hr hp.1.2
        rw [Set.indicator_of_mem ht,
          Set.indicator_of_notMem hd,
          Set.indicator_of_notMem hp_rect]
        simp
    · have hp_rect : p ∉ rect := by
        intro hp
        apply ht
        exact ⟨hp.1.1, hp.2⟩
      rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem hp_rect]
  have hpolar :
      (∫ p in unitDisk, H p) =
        ∫ p : ℝ × ℝ, rect.indicator radial p := by
    have hp := integral_comp_polarCoord_symm
      (unitDisk.indicator H)
    calc
      (∫ p in unitDisk, H p) =
          ∫ p : ℝ × ℝ, unitDisk.indicator H p := by
        rw [integral_indicator unitDisk_closed.measurableSet]
      _ = ∫ p in polarCoord.target,
            p.1 *
              unitDisk.indicator H (polarCoord.symm p) := by
        simpa only [smul_eq_mul] using hp.symm
      _ = ∫ p : ℝ × ℝ, rect.indicator radial p := by
        rw [← integral_indicator
          polarCoord.open_target.measurableSet]
        apply integral_congr_ae
        filter_upwards with p
        exact hpolar_point p
  have hsection (φ : ℝ) :
      (∫ r : ℝ, rect.indicator radial (r, φ)) =
        (Set.Ioo (-Real.pi) Real.pi).indicator
          (fun φ =>
            ∫ r in (0 : ℝ)..1,
              r * H
                (r * Real.cos φ, r * Real.sin φ)) φ := by
    by_cases hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem hφ]
      have hind :
          (fun r : ℝ => rect.indicator radial (r, φ)) =
            (Set.Ioc (0 : ℝ) 1).indicator
              (fun r =>
                r * H
                  (r * Real.cos φ, r * Real.sin φ)) := by
        funext r
        by_cases hr : r ∈ Set.Ioc (0 : ℝ) 1
        · simp [rect, radial, hr, hφ]
        · simp [rect, radial, hr, hφ]
      rw [hind, integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one]
    · rw [Set.indicator_of_notMem hφ]
      have hz :
          (fun r : ℝ => rect.indicator radial (r, φ)) = 0 := by
        funext r
        simp [rect, hφ]
      rw [hz]
      simp
  calc
    (∫ p in unitDisk, H p) =
        ∫ p : ℝ × ℝ, rect.indicator radial p := hpolar
    _ = ∫ φ : ℝ,
          ∫ r : ℝ, rect.indicator radial (r, φ) := by
      change
        (∫ p : ℝ × ℝ, rect.indicator radial p
          ∂((MeasureTheory.volume : Measure ℝ).prod
            MeasureTheory.volume)) = _
      change
        Integrable (rect.indicator radial)
          ((MeasureTheory.volume : Measure ℝ).prod
            MeasureTheory.volume) at hrect_integrable
      simpa using
        MeasureTheory.integral_prod_symm _ hrect_integrable
    _ = ∫ φ : ℝ,
          (Set.Ioo (-Real.pi) Real.pi).indicator
            (fun φ =>
              ∫ r in (0 : ℝ)..1,
                r * H
                  (r * Real.cos φ, r * Real.sin φ)) φ := by
      apply integral_congr_ae
      filter_upwards with φ
      exact hsection φ
    _ = ∫ φ in Set.Ioo (-Real.pi) Real.pi,
          ∫ r in (0 : ℝ)..1,
            r * H
              (r * Real.cos φ, r * Real.sin φ) := by
      rw [integral_indicator measurableSet_Ioo]
    _ = ∫ φ in Set.Ioc (-Real.pi) Real.pi,
          ∫ r in (0 : ℝ)..1,
            r * H
              (r * Real.cos φ, r * Real.sin φ) := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    _ = ∫ φ in -Real.pi..Real.pi,
          ∫ r in (0 : ℝ)..1,
            r * H
              (r * Real.cos φ, r * Real.sin φ) := by
      rw [intervalIntegral.integral_of_le
        (neg_le_self Real.pi_nonneg)]

private def diskIntegrand (p : ℝ × ℝ) : ℝ :=
  (1 - p.1 ^ 6 - p.2 ^ 6) * p.1 ^ 2 * p.2 ^ 2

private def polarRadial (r φ : ℝ) : ℝ :=
  (1 - r ^ 6 *
      (Real.cos φ ^ 6 + Real.sin φ ^ 6)) *
    r ^ 5 * Real.cos φ ^ 2 * Real.sin φ ^ 2

private def angleIntegral (φ : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, polarRadial r φ

private theorem volume_cube_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume a b c =
      9 * a * b * c *
        ∫ p in unitDisk, diskIntegrand p := by
  let g : ℝ × ℝ → ℝ :=
    fun q =>
      c * (1 -
        (q.1 ^ 2 / a ^ 2 + q.2 ^ 2 / b ^ 2))
  calc
    volume a b c = ∫ q in baseRegion a b, g q := by
      rfl
    _ = ∫ p in unitDisk,
          (9 * a * b * p.1 ^ 2 * p.2 ^ 2) *
            g (cubeMap a b p) :=
      cube_change_variables a b ha hb g
    _ = ∫ p in unitDisk,
          (9 * a * b * c) * diskIntegrand p := by
      apply setIntegral_congr_fun unitDisk_closed.measurableSet
      intro p hp
      have hx :
          (a * p.1 ^ 3) ^ 2 / a ^ 2 =
            p.1 ^ 6 := by
        field_simp [ha.ne']
      have hy :
          (b * p.2 ^ 3) ^ 2 / b ^ 2 =
            p.2 ^ 6 := by
        field_simp [hb.ne']
      dsimp [g, cubeMap, diskIntegrand]
      rw [hx, hy]
      ring
    _ = 9 * a * b * c *
          ∫ p in unitDisk, diskIntegrand p := by
      rw [MeasureTheory.integral_const_mul]

private theorem diskIntegrand_polar :
    (∫ p in unitDisk, diskIntegrand p) =
      ∫ φ in -Real.pi..Real.pi, angleIntegral φ := by
  have hcont : Continuous diskIntegrand := by
    unfold diskIntegrand
    fun_prop
  rw [unitDisk_polar diskIntegrand hcont]
  apply intervalIntegral.integral_congr
  intro φ hφ
  unfold angleIntegral
  apply intervalIntegral.integral_congr
  intro r hr
  unfold diskIntegrand polarRadial
  ring

private theorem angleIntegral_periodic :
    Function.Periodic angleIntegral (Real.pi / 2) := by
  intro φ
  unfold angleIntegral polarRadial
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

private theorem angleIntegral_continuous :
    Continuous angleIntegral := by
  unfold angleIntegral polarRadial
  fun_prop

private theorem angle_full_eq_four_quarters :
    (∫ φ in -Real.pi..Real.pi, angleIntegral φ) =
      4 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          angleIntegral φ := by
  have hint :
      ∀ u v : ℝ,
        IntervalIntegrable angleIntegral
          MeasureTheory.volume u v :=
    fun u v => angleIntegral_continuous.intervalIntegrable u v
  calc
    (∫ φ in -Real.pi..Real.pi, angleIntegral φ) =
        ∫ φ in -Real.pi..
          -Real.pi + (4 : ℤ) • (Real.pi / 2),
            angleIntegral φ := by
      congr 2
      norm_num
      ring
    _ = (4 : ℤ) •
          ∫ φ in -Real.pi..-Real.pi + Real.pi / 2,
            angleIntegral φ :=
      angleIntegral_periodic.intervalIntegral_add_zsmul_eq
        4 (-Real.pi) hint
    _ = 4 *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            angleIntegral φ := by
      rw [angleIntegral_periodic.intervalIntegral_add_eq
        (-Real.pi) 0]
      norm_num

private theorem radial_cube_relation (A C : ℝ) :
    (∫ ρ in (0 : ℝ)..1,
        (1 - ρ ^ 6 * A) * ρ ^ 5 * C) =
      1 / 3 *
        ∫ r in (0 : ℝ)..1,
          (1 - r ^ 2 * A) * r * C := by
  let f : ℝ → ℝ := fun ρ => ρ ^ 3
  let f' : ℝ → ℝ := fun ρ => 3 * ρ ^ 2
  let g : ℝ → ℝ :=
    fun r => (1 - r ^ 2 * A) * r * C
  have hf :
      ∀ ρ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt f (f' ρ) ρ := by
    intro ρ hρ
    dsimp [f, f']
    convert (hasDerivAt_id ρ).pow 3 using 1 <;>
      simp <;> ring
  have hf' : ContinuousOn f' (Set.uIcc (0 : ℝ) 1) := by
    exact (by fun_prop : Continuous f').continuousOn
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := 1)
      (f := f) (f' := f') (g := g) hf hf' hg
  have hleft :
      (∫ ρ in (0 : ℝ)..1,
          (1 - ρ ^ 6 * A) * ρ ^ 5 * C) =
        1 / 3 *
          ∫ ρ in (0 : ℝ)..1,
            (g ∘ f) ρ * f' ρ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro ρ hρ
    dsimp [g, f, f']
    ring
  rw [hleft, hsub]
  simp [f, g]

private theorem quarter_radial_relation :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        angleIntegral φ) =
      1 / 3 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            (1 - r ^ 2 *
                (Real.cos φ ^ 6 + Real.sin φ ^ 6)) *
              r * Real.cos φ ^ 2 * Real.sin φ ^ 2 := by
  have hpoint (φ : ℝ) :
      angleIntegral φ =
        1 / 3 *
          ∫ r in (0 : ℝ)..1,
            (1 - r ^ 2 *
                (Real.cos φ ^ 6 + Real.sin φ ^ 6)) *
              r * Real.cos φ ^ 2 * Real.sin φ ^ 2 := by
    unfold angleIntegral polarRadial
    have h :=
      radial_cube_relation
        (Real.cos φ ^ 6 + Real.sin φ ^ 6)
        (Real.cos φ ^ 2 * Real.sin φ ^ 2)
    simpa only [mul_assoc] using h
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        angleIntegral φ) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          1 / 3 *
            (∫ r in (0 : ℝ)..1,
              (1 - r ^ 2 *
                  (Real.cos φ ^ 6 + Real.sin φ ^ 6)) *
                r * Real.cos φ ^ 2 *
                  Real.sin φ ^ 2) := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      exact hpoint φ
    _ = 1 / 3 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            (1 - r ^ 2 *
                (Real.cos φ ^ 6 + Real.sin φ ^ 6)) *
              r * Real.cos φ ^ 2 * Real.sin φ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]

theorem gap7 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      12 * a * b * c *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            (1 - r ^ 2 * (Real.cos φ ^ 6 + Real.sin φ ^ 6)) *
              r * Real.cos φ ^ 2 * Real.sin φ ^ 2 := by
  rw [volume_cube_formula a b c ha hb,
    diskIntegrand_polar, angle_full_eq_four_quarters,
    quarter_radial_relation]
  ring

private theorem radial_integral (A C : ℝ) :
    (∫ r in (0 : ℝ)..1,
        (1 - r ^ 2 * A) * r * C) =
      (1 / 2 - A / 4) * C := by
  have hlin :
      IntervalIntegrable (fun r : ℝ => C * r)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hcub :
      IntervalIntegrable (fun r : ℝ => (A * C) * r ^ 3)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 1
  calc
    (∫ r in (0 : ℝ)..1, (1 - r ^ 2 * A) * r * C) =
        ∫ r in (0 : ℝ)..1, C * r - (A * C) * r ^ 3 := by
      apply intervalIntegral.integral_congr
      intro r hr
      ring
    _ = (∫ r in (0 : ℝ)..1, C * r) -
        ∫ r in (0 : ℝ)..1, (A * C) * r ^ 3 :=
      intervalIntegral.integral_sub hlin hcub
    _ = (1 / 2 - A / 4) * C := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_id, integral_pow]
      norm_num
      ring

theorem gap8 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      12 * a * b * c *
        ((∫ φ in (0 : ℝ)..Real.pi / 2,
            1 / 2 * Real.cos φ ^ 2 * Real.sin φ ^ 2) -
          1 / 4 *
            ∫ φ in (0 : ℝ)..Real.pi / 2,
              (Real.cos φ ^ 6 + Real.sin φ ^ 6) *
                Real.cos φ ^ 2 * Real.sin φ ^ 2) := by
  rw [gap7 a b c ha hb hc]
  have hpoint :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            (1 - r ^ 2 *
                (Real.cos φ ^ 6 + Real.sin φ ^ 6)) *
              r * Real.cos φ ^ 2 * Real.sin φ ^ 2) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          (1 / 2 -
              (Real.cos φ ^ 6 + Real.sin φ ^ 6) / 4) *
            (Real.cos φ ^ 2 * Real.sin φ ^ 2) := by
    apply intervalIntegral.integral_congr
    intro φ hφ
    simpa only [mul_assoc] using
      radial_integral
        (Real.cos φ ^ 6 + Real.sin φ ^ 6)
        (Real.cos φ ^ 2 * Real.sin φ ^ 2)
  rw [hpoint]
  congr 1
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        (1 / 2 -
            (Real.cos φ ^ 6 + Real.sin φ ^ 6) / 4) *
          (Real.cos φ ^ 2 * Real.sin φ ^ 2)) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          (1 / 2) *
              (Real.cos φ ^ 2 * Real.sin φ ^ 2) -
            (1 / 4) *
              ((Real.cos φ ^ 6 + Real.sin φ ^ 6) *
                Real.cos φ ^ 2 * Real.sin φ ^ 2) := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      ring
    _ = _ := by
      have hfirst :
          IntervalIntegrable
            (fun φ : ℝ =>
              (1 / 2) *
                (Real.cos φ ^ 2 * Real.sin φ ^ 2))
            MeasureTheory.volume 0 (Real.pi / 2) :=
        (by fun_prop : Continuous
          (fun φ : ℝ =>
            (1 / 2) *
              (Real.cos φ ^ 2 * Real.sin φ ^ 2))).intervalIntegrable
                0 (Real.pi / 2)
      have hsecond :
          IntervalIntegrable
            (fun φ : ℝ =>
              (1 / 4) *
                ((Real.cos φ ^ 6 + Real.sin φ ^ 6) *
                  Real.cos φ ^ 2 * Real.sin φ ^ 2))
            MeasureTheory.volume 0 (Real.pi / 2) :=
        (by fun_prop : Continuous
          (fun φ : ℝ =>
            (1 / 4) *
              ((Real.cos φ ^ 6 + Real.sin φ ^ 6) *
                Real.cos φ ^ 2 * Real.sin φ ^ 2))).intervalIntegrable
                  0 (Real.pi / 2)
      have hhalf :
          (∫ φ in (0 : ℝ)..Real.pi / 2,
              1 / 2 * Real.cos φ ^ 2 * Real.sin φ ^ 2) =
            1 / 2 *
              ∫ φ in (0 : ℝ)..Real.pi / 2,
                Real.cos φ ^ 2 * Real.sin φ ^ 2 := by
        calc
          _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
                (1 / 2) *
                  (Real.cos φ ^ 2 * Real.sin φ ^ 2) := by
            apply intervalIntegral.integral_congr
            intro φ hφ
            ring
          _ = _ := intervalIntegral.integral_const_mul
            (1 / 2 : ℝ)
            (fun φ : ℝ =>
              Real.cos φ ^ 2 * Real.sin φ ^ 2)
      rw [intervalIntegral.integral_sub hfirst hsecond,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hhalf]

private theorem reflected_mixed_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.sin φ ^ 8 * Real.cos φ ^ 2) =
      ∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.cos φ ^ 8 * Real.sin φ ^ 2 := by
  let f : ℝ → ℝ :=
    fun φ => Real.cos φ ^ 8 * Real.sin φ ^ 2
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.sin φ ^ 8 * Real.cos φ ^ 2) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          f (Real.pi / 2 - φ) := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      dsimp [f]
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    _ = ∫ φ in (0 : ℝ)..Real.pi / 2, f φ := by
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (f := f) (a := (0 : ℝ))
          (b := Real.pi / 2) (Real.pi / 2))
    _ = _ := rfl

theorem gap9 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      6 * a * b * c *
        ((∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.cos φ ^ 2 * Real.sin φ ^ 2) -
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.cos φ ^ 8 * Real.sin φ ^ 2) := by
  rw [gap8 a b c ha hb hc]
  have hmix :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          (Real.cos φ ^ 6 + Real.sin φ ^ 6) *
            Real.cos φ ^ 2 * Real.sin φ ^ 2) =
        2 *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.cos φ ^ 8 * Real.sin φ ^ 2 := by
    calc
      _ = (∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.cos φ ^ 8 * Real.sin φ ^ 2) +
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.sin φ ^ 8 * Real.cos φ ^ 2 := by
        rw [← intervalIntegral.integral_add
          ((by fun_prop : Continuous
            (fun φ : ℝ =>
              Real.cos φ ^ 8 * Real.sin φ ^ 2)).intervalIntegrable
                (0 : ℝ) (Real.pi / 2))
          ((by fun_prop : Continuous
            (fun φ : ℝ =>
              Real.sin φ ^ 8 * Real.cos φ ^ 2)).intervalIntegrable
                (0 : ℝ) (Real.pi / 2))]
        apply intervalIntegral.integral_congr
        intro φ hφ
        ring
      _ = 2 *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.cos φ ^ 8 * Real.sin φ ^ 2 := by
        rw [reflected_mixed_integral]
        ring
  rw [hmix]
  have hhalf :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          1 / 2 * Real.cos φ ^ 2 * Real.sin φ ^ 2) =
        1 / 2 *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.cos φ ^ 2 * Real.sin φ ^ 2 := by
    calc
      _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
            (1 / 2) *
              (Real.cos φ ^ 2 * Real.sin φ ^ 2) := by
        apply intervalIntegral.integral_congr
        intro φ hφ
        ring
      _ = _ := intervalIntegral.integral_const_mul
        (1 / 2 : ℝ)
        (fun φ : ℝ =>
          Real.cos φ ^ 2 * Real.sin φ ^ 2)
  rw [hhalf]
  ring

private theorem half_cos_zero :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 0) =
      Real.pi / 2 := by simp

private theorem half_cos_recurrence (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ (n + 2)) =
      (n + 1 : ℝ) / (n + 2 : ℝ) *
        ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ n := by
  rw [integral_cos_pow]
  simp

private theorem half_cos_two :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 2) =
      Real.pi / 4 := by
  rw [half_cos_recurrence 0, half_cos_zero]
  norm_num
  ring

private theorem half_cos_four :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 4) =
      3 * Real.pi / 16 := by
  rw [half_cos_recurrence 2, half_cos_two]
  norm_num
  ring

private theorem half_cos_six :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 6) =
      5 * Real.pi / 32 := by
  rw [half_cos_recurrence 4, half_cos_four]
  norm_num
  ring

private theorem half_cos_eight :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 8) =
      35 * Real.pi / 256 := by
  rw [half_cos_recurrence 6, half_cos_six]
  norm_num
  ring

private theorem half_cos_ten :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 10) =
      63 * Real.pi / 512 := by
  rw [half_cos_recurrence 8, half_cos_eight]
  norm_num
  ring

private theorem mixed_two_two :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.cos φ ^ 2 * Real.sin φ ^ 2) =
      Real.pi / 4 * (1 - 3 / 4) := by
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.cos φ ^ 2 * Real.sin φ ^ 2) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          Real.sin φ ^ 2 * Real.cos φ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      ring
    _ = Real.pi / 4 * (1 - 3 / 4) := by
      rw [integral_sin_sq_mul_cos_sq]
      rw [show 4 * (Real.pi / 2) = 2 * Real.pi by ring,
        Real.sin_two_pi]
      simp
      ring

private theorem mixed_eight_two :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.cos φ ^ 8 * Real.sin φ ^ 2) =
      1 / 10 * ((7 * 5 * 3 * 1 : ℝ) / (8 * 6 * 4 * 2)) *
        (Real.pi / 2) := by
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.cos φ ^ 8 * Real.sin φ ^ 2) =
        (∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 8) -
          ∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 10 := by
      rw [← intervalIntegral.integral_sub
        ((by fun_prop : Continuous
          (fun φ : ℝ => Real.cos φ ^ 8)).intervalIntegrable
            (0 : ℝ) (Real.pi / 2))
        ((by fun_prop : Continuous
          (fun φ : ℝ => Real.cos φ ^ 10)).intervalIntegrable
            (0 : ℝ) (Real.pi / 2))]
      apply intervalIntegral.integral_congr
      intro φ hφ
      change
        Real.cos φ ^ 8 * Real.sin φ ^ 2 =
          Real.cos φ ^ 8 - Real.cos φ ^ 10
      rw [Real.sin_sq]
      ring
    _ = _ := by
      rw [half_cos_eight, half_cos_ten]
      norm_num
      ring

theorem gap10 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      6 * a * b * c *
        (Real.pi / 4 * (1 - 3 / 4) -
          1 / 10 * ((7 * 5 * 3 * 1 : ℝ) / (8 * 6 * 4 * 2)) *
            (Real.pi / 2)) := by
  rw [gap9 a b c ha hb hc, mixed_two_two, mixed_eight_two]

theorem gap11 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      3 * Real.pi * a * b * c / 2 * (1 / 4 - 105 / 1920) := by
  rw [gap10 a b c ha hb hc]
  ring

theorem gap12 (a b c : ℝ) :
    3 * Real.pi * a * b * c / 2 * (1 / 4 - 105 / 1920) =
      75 / 256 * Real.pi * a * b * c := by
  ring

theorem gap13 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c = 75 / 256 * Real.pi * a * b * c := by
  rw [gap11 a b c ha hb hc, gap12]

end

end ProofGap.Exercise4032
