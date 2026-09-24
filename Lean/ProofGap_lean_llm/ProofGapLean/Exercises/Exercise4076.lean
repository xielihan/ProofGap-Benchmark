import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4076

noncomputable section

open MeasureTheory
open scoped Interval

def cylinder (a h : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 ≤ a ^ 2 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ h}

def distanceSq (b : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.2.1 ^ 2 + (b - p.2.2) ^ 2

def forceX (a h b k m M : ℝ) : ℝ :=
  ∫ p in cylinder a h,
    k * m * M / (Real.pi * a ^ 2 * h) *
      p.1 / Real.sqrt (distanceSq b p) ^ 3

def forceY (a h b k m M : ℝ) : ℝ :=
  ∫ p in cylinder a h,
    k * m * M / (Real.pi * a ^ 2 * h) *
      p.2.1 / Real.sqrt (distanceSq b p) ^ 3

def forceZ (a h b k m M : ℝ) : ℝ :=
  ∫ p in cylinder a h,
    -(k * m * M / (Real.pi * a ^ 2 * h) *
      (b - p.2.2) / Real.sqrt (distanceSq b p) ^ 3)

def cylindricalVolumeCoefficient (r : ℝ) : ℝ :=
  2 * Real.pi * r

def cylindricalMassCoefficient (a h M r : ℝ) : ℝ :=
  2 * M * r / (a ^ 2 * h)

def axialForceDensity (a h b k m M r z : ℝ) : ℝ :=
  -(2 * k * r * m * M * (b - z) /
    (a ^ 2 * h * Real.sqrt ((r ^ 2 + (b - z) ^ 2) ^ 3)))

private def flipX : (ℝ × ℝ × ℝ) ≃ᵐ (ℝ × ℝ × ℝ) where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv := by
    rintro ⟨x, yz⟩
    simp
  right_inv := by
    rintro ⟨x, yz⟩
    simp
  measurable_toFun := measurable_fst.neg.prodMk measurable_snd
  measurable_invFun := measurable_fst.neg.prodMk measurable_snd

private def flipY : (ℝ × ℝ × ℝ) ≃ᵐ (ℝ × ℝ × ℝ) where
  toFun p := (p.1, (-p.2.1, p.2.2))
  invFun p := (p.1, (-p.2.1, p.2.2))
  left_inv := by
    rintro ⟨x, y, z⟩
    simp
  right_inv := by
    rintro ⟨x, y, z⟩
    simp
  measurable_toFun :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).neg.prodMk
        (measurable_snd.comp measurable_snd))
  measurable_invFun :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).neg.prodMk
        (measurable_snd.comp measurable_snd))

private theorem flipX_measurePreserving :
    MeasurePreserving flipX := by
  have hneg : MeasurePreserving (fun x : ℝ => -x) := by
    refine ⟨measurable_id.neg, ?_⟩
    simpa using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  rw [Measure.volume_eq_prod]
  simpa [flipX, Prod.map] using
    hneg.prod
      (MeasurePreserving.id
        (MeasureTheory.volume : Measure (ℝ × ℝ)))

private theorem flipY_measurePreserving :
    MeasurePreserving flipY := by
  have hneg : MeasurePreserving (fun x : ℝ => -x) := by
    refine ⟨measurable_id.neg, ?_⟩
    simpa using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  have hpair : MeasurePreserving
      (fun q : ℝ × ℝ => (-q.1, q.2)) := by
    rw [Measure.volume_eq_prod]
    simpa [Prod.map] using
      hneg.prod
        (MeasurePreserving.id
          (MeasureTheory.volume : Measure ℝ))
  rw [Measure.volume_eq_prod]
  simpa [flipY, Prod.map] using
    (MeasurePreserving.id
      (MeasureTheory.volume : Measure ℝ)).prod hpair

private theorem cylinder_measurable (a h : ℝ) :
    MeasurableSet (cylinder a h) := by
  exact ((isClosed_le
      (((continuous_fst.pow 2).add
        ((continuous_fst.comp continuous_snd).pow 2)))
      continuous_const).inter
    ((isClosed_le continuous_const
        (continuous_snd.comp continuous_snd)).inter
      (isClosed_le (continuous_snd.comp continuous_snd)
        continuous_const))).measurableSet

private theorem flipX_mem_cylinder (a h : ℝ) (p : ℝ × ℝ × ℝ) :
    flipX p ∈ cylinder a h ↔ p ∈ cylinder a h := by
  rcases p with ⟨x, y, z⟩
  change
    ((-x) ^ 2 + y ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h) ↔
      (x ^ 2 + y ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h)
  ring_nf

private theorem flipY_mem_cylinder (a h : ℝ) (p : ℝ × ℝ × ℝ) :
    flipY p ∈ cylinder a h ↔ p ∈ cylinder a h := by
  rcases p with ⟨x, y, z⟩
  change
    (x ^ 2 + (-y) ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h) ↔
      (x ^ 2 + y ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h)
  ring_nf

private theorem distanceSq_flipX (b : ℝ) (p : ℝ × ℝ × ℝ) :
    distanceSq b (flipX p) = distanceSq b p := by
  rcases p with ⟨x, y, z⟩
  change
    (-x) ^ 2 + y ^ 2 + (b - z) ^ 2 =
      x ^ 2 + y ^ 2 + (b - z) ^ 2
  ring

private theorem distanceSq_flipY (b : ℝ) (p : ℝ × ℝ × ℝ) :
    distanceSq b (flipY p) = distanceSq b p := by
  rcases p with ⟨x, y, z⟩
  change
    x ^ 2 + (-y) ^ 2 + (b - z) ^ 2 =
      x ^ 2 + y ^ 2 + (b - z) ^ 2
  ring

private theorem sqrt_cube (u : ℝ) (hu : 0 ≤ u) :
    Real.sqrt (u ^ 3) = u * Real.sqrt u := by
  have hleft : 0 ≤ Real.sqrt (u ^ 3) := Real.sqrt_nonneg _
  have hright : 0 ≤ u * Real.sqrt u :=
    mul_nonneg hu (Real.sqrt_nonneg _)
  have hsqLeft : Real.sqrt (u ^ 3) ^ 2 = u ^ 3 :=
    Real.sq_sqrt (pow_nonneg hu 3)
  have hsqU : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  apply (sq_eq_sq₀ hleft hright).mp
  rw [hsqLeft, mul_pow, hsqU]
  ring

private theorem sqrt_pow_three (u : ℝ) (hu : 0 ≤ u) :
    Real.sqrt u ^ 3 = Real.sqrt (u ^ 3) := by
  calc
    Real.sqrt u ^ 3 = Real.sqrt u ^ 2 * Real.sqrt u := by ring
    _ = u * Real.sqrt u := by rw [Real.sq_sqrt hu]
    _ = Real.sqrt (u ^ 3) := (sqrt_cube u hu).symm

private theorem radial_kernel_integral (a d : ℝ) (ha : 0 < a) :
    (∫ r in (0 : ℝ)..a,
      r * d / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) =
      Real.sign d - d / Real.sqrt (a ^ 2 + d ^ 2) := by
  by_cases hd : d = 0
  · simp [hd]
  let F : ℝ → ℝ := fun r =>
    -d / Real.sqrt (r ^ 2 + d ^ 2)
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt F
        (r * d / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) r := by
    intro r _
    have hu : 0 < r ^ 2 + d ^ 2 := by
      nlinarith [sq_nonneg r]
    have hinner :
        HasDerivAt (fun x : ℝ => x ^ 2 + d ^ 2) (2 * r) r := by
      convert ((hasDerivAt_id r).pow 2).add_const (d ^ 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt :
        HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + d ^ 2))
          (1 / (2 * Real.sqrt (r ^ 2 + d ^ 2)) * (2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hu.ne').comp r hinner
    have hsqrtne : Real.sqrt (r ^ 2 + d ^ 2) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hu
    have hsquare :
        Real.sqrt (r ^ 2 + d ^ 2) ^ 2 = r ^ 2 + d ^ 2 :=
      Real.sq_sqrt hu.le
    have hcube :
        Real.sqrt ((r ^ 2 + d ^ 2) ^ 3) =
          (r ^ 2 + d ^ 2) * Real.sqrt (r ^ 2 + d ^ 2) :=
      sqrt_cube _ hu.le
    dsimp [F]
    convert (hasDerivAt_const r (-d)).div hsqrt hsqrtne using 1
    rw [hcube]
    field_simp [hsqrtne]
    rw [hsquare]
    ring
  have hcont : Continuous
      (fun r : ℝ =>
        r * d / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro r
      apply Real.sqrt_ne_zero'.mpr
      exact pow_pos (by nlinarith [sq_nonneg r]) 3
  have hFTC :
      (∫ r in (0 : ℝ)..a,
        r * d / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) =
        F a - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv (hcont.intervalIntegrable _ _)
  rw [hFTC]
  dsimp [F]
  rw [show (0 : ℝ) ^ 2 + d ^ 2 = d ^ 2 by ring,
    Real.sqrt_sq_eq_abs]
  by_cases hdpos : 0 < d
  · rw [abs_of_pos hdpos, Real.sign_of_pos hdpos]
    field_simp [hdpos.ne']
    ring
  · have hdneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hdpos) hd
    rw [abs_of_neg hdneg, Real.sign_of_neg hdneg]
    field_simp [hdneg.ne]
    ring

private theorem axial_sqrt_integral (a b h : ℝ) (ha : 0 < a) :
    (∫ z in (0 : ℝ)..h,
      (b - z) / Real.sqrt (a ^ 2 + (b - z) ^ 2)) =
      Real.sqrt (a ^ 2 + b ^ 2) -
        Real.sqrt (a ^ 2 + (b - h) ^ 2) := by
  let F : ℝ → ℝ := fun z =>
    -Real.sqrt (a ^ 2 + (b - z) ^ 2)
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hderiv : ∀ z ∈ Set.uIcc (0 : ℝ) h,
      HasDerivAt F
        ((b - z) / Real.sqrt (a ^ 2 + (b - z) ^ 2)) z := by
    intro z _
    have hu : 0 < a ^ 2 + (b - z) ^ 2 := by
      nlinarith [sq_nonneg (b - z)]
    have hlin :
        HasDerivAt (fun x : ℝ => b - x) (-1) z := by
      convert (hasDerivAt_const z b).sub (hasDerivAt_id z) using 1 <;>
        ring
    have hinner :
        HasDerivAt (fun x : ℝ => a ^ 2 + (b - x) ^ 2)
          (-2 * (b - z)) z := by
      convert (hasDerivAt_const z (a ^ 2)).add (hlin.pow 2) using 1 <;>
        ring
    have hsqrt :
        HasDerivAt
          (fun x : ℝ => Real.sqrt (a ^ 2 + (b - x) ^ 2))
          (1 / (2 * Real.sqrt (a ^ 2 + (b - z) ^ 2)) *
            (-2 * (b - z))) z := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hu.ne').comp z hinner
    dsimp [F]
    convert hsqrt.neg using 1
    field_simp [Real.sqrt_ne_zero'.mpr hu]
  have hcont : Continuous
      (fun z : ℝ =>
        (b - z) / Real.sqrt (a ^ 2 + (b - z) ^ 2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z
      apply Real.sqrt_ne_zero'.mpr
      nlinarith [sq_nonneg (b - z)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (hcont.intervalIntegrable _ _)]
  dsimp [F]
  simp only [sub_zero]
  ring

private theorem sign_intervalIntegrable (b s t : ℝ) :
    IntervalIntegrable (fun z : ℝ => Real.sign (b - z))
      MeasureTheory.volume s t := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M := 1)
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  · have hm : Measurable (fun z : ℝ => Real.sign (b - z)) := by
      unfold Real.sign
      have harg : Measurable (fun z : ℝ => b - z) :=
        measurable_const.sub measurable_id
      exact Measurable.ite (measurableSet_lt harg measurable_const)
        measurable_const
        (Measurable.ite (measurableSet_lt measurable_const harg)
          measurable_const measurable_const)
    exact hm.aestronglyMeasurable
  · filter_upwards [] with z
    rcases Real.sign_apply_eq (b - z) with hz | hz | hz
    · simp [hz]
    · simp [hz]
    · simp [hz]

private theorem sign_integral_positive (s t b : ℝ)
    (hst : s < t) (htb : t ≤ b) :
    (∫ z in s..t, Real.sign (b - z)) = t - s := by
  have hae : ∀ᵐ z : ℝ ∂MeasureTheory.volume,
      z ∈ Set.uIoc s t →
        Real.sign (b - z) = (1 : ℝ) := by
    filter_upwards [MeasureTheory.volume.ae_ne b] with z hzb hz
    rw [Set.uIoc_of_le hst.le] at hz
    rw [Real.sign_of_pos]
    have : z < b := lt_of_le_of_ne (hz.2.trans htb) hzb
    linarith
  rw [intervalIntegral.integral_congr_ae hae]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem sign_integral_negative (s t b : ℝ)
    (hst : s < t) (hbs : b ≤ s) :
    (∫ z in s..t, Real.sign (b - z)) = -(t - s) := by
  have hae : ∀ᵐ z : ℝ ∂MeasureTheory.volume,
      z ∈ Set.uIoc s t →
        Real.sign (b - z) = (-1 : ℝ) := by
    filter_upwards [MeasureTheory.volume.ae_ne b] with z hzb hz
    rw [Set.uIoc_of_le hst.le] at hz
    rw [Real.sign_of_neg]
    have : b < z := lt_of_le_of_ne (hbs.trans hz.1.le) (Ne.symm hzb)
    linarith
  rw [intervalIntegral.integral_congr_ae hae]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem sign_affine_integral (b h : ℝ) (hh : 0 < h) :
    (∫ z in (0 : ℝ)..h, Real.sign (b - z)) =
      |b| - |b - h| := by
  by_cases hb0 : b ≤ 0
  · rw [sign_integral_negative 0 h b hh hb0,
      abs_of_nonpos hb0,
      abs_of_neg (by linarith : b - h < 0)]
    ring
  by_cases hhb : h ≤ b
  · rw [sign_integral_positive 0 h b hh hhb,
      abs_of_pos (lt_of_lt_of_le hh hhb),
      abs_of_nonneg (sub_nonneg.mpr hhb)]
    ring
  have hbpos : 0 < b := lt_of_not_ge hb0
  have hblt : b < h := lt_of_not_ge hhb
  have hleft := sign_integral_positive 0 b b hbpos le_rfl
  have hright := sign_integral_negative b h b
    (sub_pos.mp (sub_pos.mpr hblt)) le_rfl
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals
      (sign_intervalIntegrable b 0 b)
      (sign_intervalIntegrable b b h)
  rw [hleft, hright] at hsplit
  rw [← hsplit, abs_of_pos hbpos, abs_of_neg (sub_neg.mpr hblt)]
  ring

private def disk (a : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2}

private def planeNorm (d : ℝ) (q : ℝ × ℝ) : ℝ :=
  |d| / Real.sqrt ((q.1 ^ 2 + q.2 ^ 2 + d ^ 2) ^ 3)

private theorem disk_closed (a : ℝ) : IsClosed (disk a) := by
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem disk_compact (a : ℝ) (ha : 0 < a) :
    IsCompact (disk a) := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc (-a, -a) (a, a))).of_isClosed_subset
      (disk_closed a)
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2 at hq
  have hx : q.1 ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg q.2]
  have hy : q.2 ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg q.1]
  exact ⟨⟨by nlinarith [sq_nonneg (q.1 + a)],
      by nlinarith [sq_nonneg (q.2 + a)]⟩,
    ⟨by nlinarith [sq_nonneg (q.1 - a)],
      by nlinarith [sq_nonneg (q.2 - a)]⟩⟩

private theorem angular_full :
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

private theorem planeNorm_polar_pointwise (a d : ℝ) (ha : 0 < a)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • (disk a).indicator (planeNorm d) (polarCoord.symm p) =
      (Set.Iic a).indicator
          (fun r =>
            r * |d| / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) p.1 *
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
      polarCoord.symm (r, theta) ∈ disk a ↔ r ≤ a := by
    rw [polarCoord_symm_apply]
    simp only [disk, Set.mem_setOf_eq]
    rw [htrig]
    exact (sq_le_sq₀ hr.le ha.le)
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases hra : r ≤ a
  · simp only [hra, if_true, mul_one]
    rw [polarCoord_symm_apply]
    unfold planeNorm
    rw [htrig]
    ring
  · simp [hra]

private theorem planeNorm_integral (a d : ℝ)
    (ha : 0 < a) (hd : d ≠ 0) :
    (∫ q in disk a, planeNorm d q) =
      2 * Real.pi *
        (1 - |d| / Real.sqrt (a ^ 2 + d ^ 2)) := by
  have hp := integral_comp_polarCoord_symm
    ((disk a).indicator (planeNorm d))
  rw [integral_indicator (disk_closed a).measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • (disk a).indicator (planeNorm d)
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic a).indicator
              (fun r =>
                r * |d| /
                  Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) r) *
          ∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic a).indicator
              (fun r =>
                r * |d| /
                  Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) p.1 *
            (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact planeNorm_polar_pointwise a d ha p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic a).indicator
              (fun r =>
                r * |d| /
                  Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) r)
          (fun _theta : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic a).indicator
            (fun r =>
              r * |d| /
                Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) r) =
        ∫ r in (0 : ℝ)..a,
          r * |d| / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3) := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic a = Set.Ioc (0 : ℝ) a := by
      ext r
      simp
    rw [hinter, intervalIntegral.integral_of_le ha.le]
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hsquared : |d| ^ 2 = d ^ 2 := sq_abs d
  have hkernel := radial_kernel_integral a |d| ha
  rw [Real.sign_of_pos hdabs, hsquared] at hkernel
  rw [hprod, hrad, angular_full, hkernel] at hp
  nlinarith [Real.pi_pos]

private theorem planeNorm_integral_le (a d : ℝ)
    (ha : 0 < a) (hd : d ≠ 0) :
    (∫ q in disk a, planeNorm d q) ≤ 2 * Real.pi := by
  rw [planeNorm_integral a d ha hd]
  have hratio : 0 ≤ |d| / Real.sqrt (a ^ 2 + d ^ 2) :=
    div_nonneg (abs_nonneg d) (Real.sqrt_nonneg _)
  exact mul_le_of_le_one_right (by positivity : 0 ≤ 2 * Real.pi)
    (by linarith)

private def axialPlane (d : ℝ) (q : ℝ × ℝ) : ℝ :=
  d / Real.sqrt ((q.1 ^ 2 + q.2 ^ 2 + d ^ 2) ^ 3)

private def axialProduct (a h b : ℝ)
    (p : (ℝ × ℝ) × ℝ) : ℝ :=
  (disk a ×ˢ Set.Icc (0 : ℝ) h).indicator
    (fun p => axialPlane (b - p.2) p.1) p

private theorem axialProduct_integrable (a h b : ℝ)
    (ha : 0 < a) (hh : 0 < h) :
    Integrable (axialProduct a h b) := by
  have hset : MeasurableSet
      (disk a ×ˢ Set.Icc (0 : ℝ) h) :=
    (disk_closed a).measurableSet.prod measurableSet_Icc
  have hraw : Measurable
      (fun p : (ℝ × ℝ) × ℝ =>
        axialPlane (b - p.2) p.1) := by
    unfold axialPlane
    measurability
  have hmeas : AEStronglyMeasurable (axialProduct a h b) :=
    (hraw.indicator hset).aestronglyMeasurable
  rw [Measure.volume_eq_prod] at hmeas ⊢
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [MeasureTheory.volume.ae_ne b] with z hzb
    by_cases hz : z ∈ Set.Icc (0 : ℝ) h
    · have hd : b - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzb)
      have hcont : Continuous (axialPlane (b - z)) := by
        unfold axialPlane
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro q
          apply Real.sqrt_ne_zero'.mpr
          apply pow_pos
          have hd2 : 0 < (b - z) ^ 2 := sq_pos_of_ne_zero hd
          nlinarith [sq_nonneg q.1, sq_nonneg q.2]
      have hi : Integrable ((disk a).indicator
          (axialPlane (b - z))) :=
        (hcont.continuousOn.integrableOn_compact (disk_compact a ha))
          |>.integrable_indicator (disk_closed a).measurableSet
      convert hi using 1
      funext q
      by_cases hq : q ∈ disk a
      · have hp :
            (q, z) ∈ disk a ×ˢ Set.Icc (0 : ℝ) h := ⟨hq, hz⟩
        unfold axialProduct
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
      · have hp :
            (q, z) ∉ disk a ×ˢ Set.Icc (0 : ℝ) h := by
          intro hp'
          exact hq hp'.1
        unfold axialProduct
        rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem hq]
    · have hzero :
          (fun q : ℝ × ℝ => axialProduct a h b (q, z)) =
            fun _q => (0 : ℝ) := by
        funext q
        simp [axialProduct, hz, Set.mem_prod]
      rw [hzero]
      exact integrable_zero _ _ _
  · let D : ℝ → ℝ :=
      (Set.Icc (0 : ℝ) h).indicator (fun _z => 2 * Real.pi)
    have hD : Integrable D := by
      have hc : IntegrableOn (fun _z : ℝ => 2 * Real.pi)
          (Set.Icc (0 : ℝ) h) :=
        continuous_const.continuousOn.integrableOn_compact isCompact_Icc
      exact hc.integrable_indicator measurableSet_Icc
    have hgmeas : AEStronglyMeasurable
        (fun z : ℝ =>
          ∫ q : ℝ × ℝ, ‖axialProduct a h b (q, z)‖) :=
      hmeas.norm.prod_swap.integral_prod_right'
    refine hD.mono' hgmeas ?_
    filter_upwards [MeasureTheory.volume.ae_ne b] with z hzb
    by_cases hz : z ∈ Set.Icc (0 : ℝ) h
    · have hd : b - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzb)
      have heq :
          (∫ q : ℝ × ℝ, ‖axialProduct a h b (q, z)‖) =
            ∫ q in disk a, planeNorm (b - z) q := by
        rw [← integral_indicator (disk_closed a).measurableSet]
        apply integral_congr_ae
        filter_upwards [] with q
        by_cases hq : q ∈ disk a
        · rw [Set.indicator_of_mem hq]
          have hu :
              0 < q.1 ^ 2 + q.2 ^ 2 + (b - z) ^ 2 := by
            have hd2 : 0 < (b - z) ^ 2 := sq_pos_of_ne_zero hd
            nlinarith [sq_nonneg q.1, sq_nonneg q.2]
          simp only [axialProduct, Set.indicator,
            Set.mem_prod, hq, hz, and_self, if_true]
          unfold axialPlane planeNorm
          rw [Real.norm_eq_abs, abs_div,
            abs_of_pos (Real.sqrt_pos.2 (pow_pos hu 3))]
        · rw [Set.indicator_of_notMem hq]
          simp [axialProduct, hq, Set.mem_prod]
      have hnonneg :
          0 ≤ ∫ q : ℝ × ℝ, ‖axialProduct a h b (q, z)‖ :=
        integral_nonneg fun _q => norm_nonneg _
      change
        (∫ q : ℝ × ℝ, |axialProduct a h b (q, z)|) =
          ∫ q in disk a, planeNorm (b - z) q at heq
      have hnonneg' :
          0 ≤ ∫ q : ℝ × ℝ, |axialProduct a h b (q, z)| := by
        simpa only [Real.norm_eq_abs] using hnonneg
      dsimp [D]
      rw [abs_of_nonneg hnonneg',
        Set.indicator_of_mem hz, heq]
      exact planeNorm_integral_le a (b - z) ha hd
    · have hzero :
          (fun q : ℝ × ℝ => axialProduct a h b (q, z)) =
            fun _q => (0 : ℝ) := by
        funext q
        simp [axialProduct, hz, Set.mem_prod]
      dsimp [D]
      rw [Set.indicator_of_notMem hz]
      have hzq : ∀ q : ℝ × ℝ,
          axialProduct a h b (q, z) = 0 :=
        fun q => congrFun hzero q
      simp_rw [hzq]
      simp

private theorem axialPlane_polar_pointwise (a d : ℝ) (ha : 0 < a)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • (disk a).indicator (axialPlane d) (polarCoord.symm p) =
      (Set.Iic a).indicator
          (fun r =>
            r * d / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) p.1 *
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
      polarCoord.symm (r, theta) ∈ disk a ↔ r ≤ a := by
    rw [polarCoord_symm_apply]
    simp only [disk, Set.mem_setOf_eq]
    rw [htrig]
    exact (sq_le_sq₀ hr.le ha.le)
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases hra : r ≤ a
  · simp only [hra, if_true, mul_one]
    rw [polarCoord_symm_apply]
    unfold axialPlane
    rw [htrig]
    ring
  · simp [hra]

private theorem axialPlane_integral (a d : ℝ) (ha : 0 < a) :
    (∫ q in disk a, axialPlane d q) =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..a,
          r * d / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3) := by
  have hp := integral_comp_polarCoord_symm
    ((disk a).indicator (axialPlane d))
  rw [integral_indicator (disk_closed a).measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • (disk a).indicator (axialPlane d)
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic a).indicator
              (fun r =>
                r * d /
                  Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) r) *
          ∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic a).indicator
              (fun r =>
                r * d /
                  Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) p.1 *
            (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact axialPlane_polar_pointwise a d ha p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic a).indicator
              (fun r =>
                r * d /
                  Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) r)
          (fun _theta : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic a).indicator
            (fun r =>
              r * d /
                Real.sqrt ((r ^ 2 + d ^ 2) ^ 3)) r) =
        ∫ r in (0 : ℝ)..a,
          r * d / Real.sqrt ((r ^ 2 + d ^ 2) ^ 3) := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic a = Set.Ioc (0 : ℝ) a := by
      ext r
      simp
    rw [hinter, intervalIntegral.integral_of_le ha.le]
  rw [hprod, hrad, angular_full] at hp
  nlinarith [Real.pi_pos]

private theorem axialCylinder_integral (a h b : ℝ)
    (ha : 0 < a) (hh : 0 < h) :
    (∫ p in cylinder a h,
        (b - p.2.2) / Real.sqrt (distanceSq b p) ^ 3) =
      2 * Real.pi *
        ∫ z in (0 : ℝ)..h,
          ∫ r in (0 : ℝ)..a,
            r * (b - z) /
              Real.sqrt ((r ^ 2 + (b - z) ^ 2) ^ 3) := by
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    (b - p.2.2) / Real.sqrt (distanceSq b p) ^ 3
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hcyl : MeasurableSet (cylinder a h) := by
    exact ((isClosed_le
        (((continuous_fst.pow 2).add
          ((continuous_fst.comp continuous_snd).pow 2)))
        continuous_const).inter
      ((isClosed_le continuous_const
          (continuous_snd.comp continuous_snd)).inter
        (isClosed_le (continuous_snd.comp continuous_snd)
          continuous_const))).measurableSet
  have hind :
      (fun q : (ℝ × ℝ) × ℝ =>
        (cylinder a h).indicator G (e q)) =
        axialProduct a h b := by
    funext q
    rcases q with ⟨⟨x, y⟩, z⟩
    have hmem :
        e ((x, y), z) ∈ cylinder a h ↔
          ((x, y), z) ∈ disk a ×ˢ Set.Icc (0 : ℝ) h := by
      change
        (x ^ 2 + y ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h) ↔
          ((x, y) ∈ disk a ∧ z ∈ Set.Icc (0 : ℝ) h)
      simp only [disk, Set.mem_setOf_eq, Set.mem_Icc]
    by_cases hp :
        ((x, y), z) ∈ disk a ×ˢ Set.Icc (0 : ℝ) h
    · have hecyl : e ((x, y), z) ∈ cylinder a h :=
        hmem.mpr hp
      rw [Set.indicator_of_mem hecyl]
      unfold axialProduct
      rw [Set.indicator_of_mem hp]
      dsimp [G, e]
      unfold axialPlane distanceSq
      change
        (b - z) /
            Real.sqrt (x ^ 2 + y ^ 2 + (b - z) ^ 2) ^ 3 =
          (b - z) /
            Real.sqrt ((x ^ 2 + y ^ 2 + (b - z) ^ 2) ^ 3)
      rw [sqrt_pow_three]
      positivity
    · have hecyl : e ((x, y), z) ∉ cylinder a h := by
        intro he
        exact hp (hmem.mp he)
      rw [Set.indicator_of_notMem hecyl]
      unfold axialProduct
      rw [Set.indicator_of_notMem hp]
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ,
          (cylinder a h).indicator G (e q)) =
        ∫ p : ℝ × (ℝ × ℝ), (cylinder a h).indicator G p :=
    volume_preserving_prodAssoc.integral_comp'
      ((cylinder a h).indicator G)
  rw [hind] at hreassoc
  rw [← integral_indicator hcyl]
  change (∫ p : ℝ × (ℝ × ℝ),
    (cylinder a h).indicator G p) = _
  rw [← hreassoc]
  have hFubini :
      (∫ q : (ℝ × ℝ) × ℝ, axialProduct a h b q) =
        ∫ z : ℝ, ∫ q : ℝ × ℝ, axialProduct a h b (q, z) := by
    exact MeasureTheory.integral_prod_symm
      (axialProduct a h b) (axialProduct_integrable a h b ha hh)
  rw [hFubini]
  have hsection (z : ℝ) :
      (∫ q : ℝ × ℝ, axialProduct a h b (q, z)) =
        (Set.Icc (0 : ℝ) h).indicator
          (fun z =>
            2 * Real.pi *
              ∫ r in (0 : ℝ)..a,
                r * (b - z) /
                  Real.sqrt ((r ^ 2 + (b - z) ^ 2) ^ 3)) z := by
    by_cases hz : z ∈ Set.Icc (0 : ℝ) h
    · rw [Set.indicator_of_mem hz]
      have hpoint :
          (fun q : ℝ × ℝ =>
            (disk a).indicator (axialPlane (b - z)) q) =
            fun q : ℝ × ℝ => axialProduct a h b (q, z) := by
        funext q
        by_cases hq : q ∈ disk a
        · have hp :
              (q, z) ∈ disk a ×ˢ Set.Icc (0 : ℝ) h := ⟨hq, hz⟩
          simp [axialProduct, hq, hp]
        · have hp :
              (q, z) ∉ disk a ×ˢ Set.Icc (0 : ℝ) h := by
            intro hp'
            exact hq hp'.1
          simp [axialProduct, hq, hp]
      rw [← hpoint, integral_indicator (disk_closed a).measurableSet,
        axialPlane_integral a (b - z) ha]
    · rw [Set.indicator_of_notMem hz]
      have hzero :
          (fun q : ℝ × ℝ => axialProduct a h b (q, z)) =
            fun _q => (0 : ℝ) := by
        funext q
        simp [axialProduct, hz, Set.mem_prod]
      rw [hzero]
      simp
  simp_rw [hsection]
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hh.le]
  rw [intervalIntegral.integral_const_mul]

theorem gap1 (a h b k m M : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceX a h b k m M = 0 := by
  unfold forceX
  rw [← integral_indicator (cylinder_measurable a h)]
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    k * m * M / (Real.pi * a ^ 2 * h) *
      p.1 / Real.sqrt (distanceSq b p) ^ 3
  change (∫ p : ℝ × (ℝ × ℝ),
    (cylinder a h).indicator G p) = 0
  have hodd :
      (fun p : ℝ × (ℝ × ℝ) =>
        (cylinder a h).indicator G (flipX p)) =
        fun p => -((cylinder a h).indicator G p) := by
    funext p
    by_cases hp : p ∈ cylinder a h
    · have hfp : flipX p ∈ cylinder a h :=
        (flipX_mem_cylinder a h p).mpr hp
      rw [Set.indicator_of_mem hfp, Set.indicator_of_mem hp]
      dsimp [G]
      rw [distanceSq_flipX]
      change
        k * m * M / (Real.pi * a ^ 2 * h) *
              (-p.1) / Real.sqrt (distanceSq b p) ^ 3 =
          -(k * m * M / (Real.pi * a ^ 2 * h) *
              p.1 / Real.sqrt (distanceSq b p) ^ 3)
      ring
    · have hfp : flipX p ∉ cylinder a h := by
        intro hfp'
        exact hp ((flipX_mem_cylinder a h p).mp hfp')
      rw [Set.indicator_of_notMem hfp,
        Set.indicator_of_notMem hp, neg_zero]
  have hchange :=
    flipX_measurePreserving.integral_comp'
      ((cylinder a h).indicator G)
  rw [hodd, integral_neg] at hchange
  linarith

theorem gap2 (a h b k m M : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceY a h b k m M = 0 := by
  unfold forceY
  rw [← integral_indicator (cylinder_measurable a h)]
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    k * m * M / (Real.pi * a ^ 2 * h) *
      p.2.1 / Real.sqrt (distanceSq b p) ^ 3
  change (∫ p : ℝ × (ℝ × ℝ),
    (cylinder a h).indicator G p) = 0
  have hodd :
      (fun p : ℝ × (ℝ × ℝ) =>
        (cylinder a h).indicator G (flipY p)) =
        fun p => -((cylinder a h).indicator G p) := by
    funext p
    by_cases hp : p ∈ cylinder a h
    · have hfp : flipY p ∈ cylinder a h :=
        (flipY_mem_cylinder a h p).mpr hp
      rw [Set.indicator_of_mem hfp, Set.indicator_of_mem hp]
      dsimp [G]
      rw [distanceSq_flipY]
      change
        k * m * M / (Real.pi * a ^ 2 * h) *
              (-p.2.1) / Real.sqrt (distanceSq b p) ^ 3 =
          -(k * m * M / (Real.pi * a ^ 2 * h) *
              p.2.1 / Real.sqrt (distanceSq b p) ^ 3)
      ring
    · have hfp : flipY p ∉ cylinder a h := by
        intro hfp'
        exact hp ((flipY_mem_cylinder a h p).mp hfp')
      rw [Set.indicator_of_notMem hfp,
        Set.indicator_of_notMem hp, neg_zero]
  have hchange :=
    flipY_measurePreserving.integral_comp'
      ((cylinder a h).indicator G)
  rw [hodd, integral_neg] at hchange
  linarith

theorem gap3 (r : ℝ) :
    cylindricalVolumeCoefficient r = 2 * Real.pi * r := by
  rfl

theorem gap4 (a h M r : ℝ) (ha : 0 < a) (hh : 0 < h) :
    cylindricalMassCoefficient a h M r =
      2 * M * r / (a ^ 2 * h) := by
  rfl

theorem gap5 (a h b k m M r z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    axialForceDensity a h b k m M r z =
      -(2 * k * r * m * M * (b - z) /
        (a ^ 2 * h *
          Real.sqrt ((r ^ 2 + (b - z) ^ 2) ^ 3))) := by
  rfl

theorem gap6 (a h b k m M : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceZ a h b k m M =
      -(2 * k * m * M / (a ^ 2 * h)) *
        ∫ z in (0 : ℝ)..h,
          ∫ r in (0 : ℝ)..a,
            r * (b - z) /
              Real.sqrt ((r ^ 2 + (b - z) ^ 2) ^ 3) := by
  let C : ℝ := k * m * M / (Real.pi * a ^ 2 * h)
  let K : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    (b - p.2.2) / Real.sqrt (distanceSq b p) ^ 3
  have hfun :
      (fun p : ℝ × (ℝ × ℝ) =>
        -(k * m * M / (Real.pi * a ^ 2 * h) *
          (b - p.2.2) / Real.sqrt (distanceSq b p) ^ 3)) =
        fun p => (-C) * K p := by
    funext p
    dsimp [C, K]
    ring
  unfold forceZ
  rw [hfun, MeasureTheory.integral_const_mul,
    axialCylinder_integral a h b ha hh]
  dsimp [C]
  field_simp [Real.pi_ne_zero, ha.ne', hh.ne']

theorem gap7 (a h b k m M : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceZ a h b k m M =
      -(2 * k * m * M / (a ^ 2 * h)) *
        ((∫ z in (0 : ℝ)..h, Real.sign (b - z)) -
          ∫ z in (0 : ℝ)..h,
            (b - z) / Real.sqrt (a ^ 2 + (b - z) ^ 2)) := by
  rw [gap6 a h b k m M ha hh]
  congr 1
  simp_rw [radial_kernel_integral a (b - _) ha]
  rw [intervalIntegral.integral_sub
    (sign_intervalIntegrable b 0 h)]
  apply Continuous.intervalIntegrable
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [sq_nonneg (b - z), sq_pos_of_pos ha]

theorem gap8 (a h b k m M : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceZ a h b k m M =
      -(2 * k * m * M / (a ^ 2 * h)) *
        (|b| - |b - h| +
          Real.sqrt (a ^ 2 + (b - h) ^ 2) -
          Real.sqrt (a ^ 2 + b ^ 2)) := by
  rw [gap7 a h b k m M ha hh,
    sign_affine_integral b h hh,
    axial_sqrt_integral a b h ha]
  ring

end

end ProofGap.Exercise4076
