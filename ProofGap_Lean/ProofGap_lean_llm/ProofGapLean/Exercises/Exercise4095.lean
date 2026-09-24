import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4095

noncomputable section

open MeasureTheory
open scoped Interval

def ellipsoid (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 +
    p.2.2 ^ 2 / c ^ 2 ≤ 1}

def radialExponential (a b c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  Real.exp
    (Real.sqrt
      (p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 +
        p.2.2 ^ 2 / c ^ 2))

def volume (a b c : ℝ) : ℝ :=
  ∫ _ in ellipsoid a b c, (1 : ℝ)

def average (a b c : ℝ) : ℝ :=
  (∫ p in ellipsoid a b c, radialExponential a b c p) /
    volume a b c

private def unitBall : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1}

private def unitDisk : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ 1}

private def halfDisk : Set (ℝ × ℝ) :=
  {q | 0 < q.1 ∧ q.1 ^ 2 + q.2 ^ 2 ≤ 1}

private def scale1 (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

private def scale3 (a b c : ℝ) :
    (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ)) :=
  (scale1 a).prodMap ((scale1 b).prodMap (scale1 c))

@[simp] private theorem scale1_apply (a x : ℝ) :
    scale1 a x = a * x := by
  simp [scale1]

@[simp] private theorem scale3_apply (a b c : ℝ)
    (p : ℝ × (ℝ × ℝ)) :
    scale3 a b c p = (a * p.1, (b * p.2.1, c * p.2.2)) := by
  rcases p with ⟨x, y, z⟩
  simp [scale3]

private theorem det_scale1 (a : ℝ) :
    (scale1 a).det = a := by
  rw [ContinuousLinearMap.det]
  rw [LinearMap.det_ring]
  simp [scale1]

private theorem det_scale3 (a b c : ℝ) :
    (scale3 a b c).det = a * b * c := by
  unfold scale3
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap,
    LinearMap.det_prodMap, ContinuousLinearMap.coe_prodMap,
    LinearMap.det_prodMap]
  change (scale1 a).det * ((scale1 b).det * (scale1 c).det) = _
  rw [det_scale1, det_scale1, det_scale1]
  ring

private theorem unitBall_closed : IsClosed unitBall := by
  exact isClosed_le
    (((continuous_fst.pow 2).add
      ((continuous_fst.comp continuous_snd).pow 2)).add
      ((continuous_snd.comp continuous_snd).pow 2))
    continuous_const

private theorem unitBall_compact : IsCompact unitBall := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc ((-1 : ℝ), ((-1 : ℝ), (-1 : ℝ)))
      ((1 : ℝ), ((1 : ℝ), (1 : ℝ))))).of_isClosed_subset unitBall_closed
  intro p hp
  change p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1 at hp
  have hx : p.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2]
  have hy : p.2.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.2]
  have hz : p.2.2 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
  constructor
  · exact ⟨by nlinarith [sq_nonneg (p.1 + 1)],
      by nlinarith [sq_nonneg (p.2.1 + 1)],
      by nlinarith [sq_nonneg (p.2.2 + 1)]⟩
  · exact ⟨by nlinarith [sq_nonneg (p.1 - 1)],
      by nlinarith [sq_nonneg (p.2.1 - 1)],
      by nlinarith [sq_nonneg (p.2.2 - 1)]⟩

private theorem scale_image_unitBall (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    scale3 a b c '' unitBall = ellipsoid a b c := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hx : (a * p.1) ^ 2 / a ^ 2 = p.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * p.2.1) ^ 2 / b ^ 2 = p.2.1 ^ 2 := by
      field_simp [hb.ne']
    have hz : (c * p.2.2) ^ 2 / c ^ 2 = p.2.2 ^ 2 := by
      field_simp [hc.ne']
    simpa [unitBall, ellipsoid, hx, hy, hz] using hp
  · intro hq
    let p : ℝ × (ℝ × ℝ) :=
      (q.1 / a, (q.2.1 / b, q.2.2 / c))
    have hmap : scale3 a b c p = q := by
      simp only [scale3_apply]
      apply Prod.ext
      · dsimp [p]
        field_simp [ha.ne']
      · apply Prod.ext
        · dsimp [p]
          field_simp [hb.ne']
        · dsimp [p]
          field_simp [hc.ne']
    refine ⟨p, ?_, hmap⟩
    have hx : (q.1 / a) ^ 2 = q.1 ^ 2 / a ^ 2 := by ring
    have hy : (q.2.1 / b) ^ 2 = q.2.1 ^ 2 / b ^ 2 := by ring
    have hz : (q.2.2 / c) ^ 2 = q.2.2 ^ 2 / c ^ 2 := by ring
    simpa [unitBall, ellipsoid, p, hx, hy, hz] using hq

private theorem scale3_injOn (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Set.InjOn (scale3 a b c) unitBall := by
  intro p hp q hq heq
  have h1 : a * p.1 = a * q.1 := by
    simpa using congrArg Prod.fst heq
  have h21 : b * p.2.1 = b * q.2.1 := by
    simpa using congrArg (fun t => t.2.1) heq
  have h22 : c * p.2.2 = c * q.2.2 := by
    simpa using congrArg (fun t => t.2.2) heq
  apply Prod.ext
  · exact mul_left_cancel₀ ha.ne' h1
  · apply Prod.ext
    · exact mul_left_cancel₀ hb.ne' h21
    · exact mul_left_cancel₀ hc.ne' h22

private theorem scale_set_integral
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (g : ℝ × ℝ × ℝ → ℝ) :
    (∫ p in ellipsoid a b c, g p) =
      ∫ p in unitBall, a * b * c * g (scale3 a b c p) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ))) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) unitBall_closed.measurableSet
      (f := scale3 a b c) (f' := fun _ => scale3 a b c)
      (fun p hp => (scale3 a b c).hasFDerivAt.hasFDerivWithinAt)
      (scale3_injOn a b c ha hb hc) g
  rw [scale_image_unitBall a b c ha hb hc] at hchange
  have habc : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  simpa only [det_scale3, abs_of_pos habc, smul_eq_mul] using hchange

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

private theorem angular_half_cos :
    (∫ theta in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
        Real.cos theta) = 2 := by
  calc
    _ = ∫ theta in Set.Ioc (-(Real.pi / 2)) (Real.pi / 2),
        Real.cos theta :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun theta : ℝ => Real.cos theta)).symm
    _ = ∫ theta in -(Real.pi / 2)..Real.pi / 2,
        Real.cos theta := by
      rw [intervalIntegral.integral_of_le]
      linarith [Real.pi_nonneg]
    _ = 2 := by
      rw [integral_cos]
      rw [Real.sin_pi_div_two, Real.sin_neg]
      norm_num

private theorem polar_xy_pointwise (F : ℝ → ℝ) (z : ℝ)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • unitBall.indicator
        (fun q : ℝ × ℝ × ℝ =>
          F (Real.sqrt (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2)))
        ((polarCoord.symm p).1, ((polarCoord.symm p).2, z)) =
      unitDisk.indicator
          (fun q : ℝ × ℝ =>
            q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
          (p.1, z) * (1 : ℝ) := by
  rcases p with ⟨r, theta⟩
  have htrig : (r * Real.cos theta) ^ 2 +
      (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      ((polarCoord.symm (r, theta)).1,
          ((polarCoord.symm (r, theta)).2, z)) ∈ unitBall ↔
        (r, z) ∈ unitDisk := by
    rw [polarCoord_symm_apply]
    simp only [unitBall, unitDisk, Set.mem_setOf_eq]
    rw [show
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 + z ^ 2 =
        ((r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2) + z ^ 2 by ring,
      htrig]
  by_cases h : (r, z) ∈ unitDisk
  · have h' :
        ((polarCoord.symm (r, theta)).1,
          ((polarCoord.symm (r, theta)).2, z)) ∈ unitBall :=
      hmem.mpr h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    simp only [smul_eq_mul]
    rw [polarCoord_symm_apply]
    rw [show
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 + z ^ 2 =
        ((r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2) + z ^ 2 by ring,
      htrig]
    ring
  · have h' :
        ((polarCoord.symm (r, theta)).1,
          ((polarCoord.symm (r, theta)).2, z)) ∉ unitBall := by
      intro hh
      exact h (hmem.mp hh)
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    simp

private theorem cos_pos_iff_in_half
    {theta : ℝ} (htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi) :
    0 < Real.cos theta ↔
      theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor
  · intro hc
    constructor
    · by_contra hn
      have hle : theta ≤ -(Real.pi / 2) := le_of_not_gt hn
      have hneg : Real.cos theta ≤ 0 := by
        rw [← Real.cos_neg theta]
        have h1 : Real.pi / 2 ≤ -theta := by linarith
        have h2 : -theta ≤ Real.pi + Real.pi / 2 := by
          linarith [htheta.1, Real.pi_pos]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
      linarith
    · by_contra hn
      have hle : Real.pi / 2 ≤ theta := le_of_not_gt hn
      have h2 : theta ≤ Real.pi + Real.pi / 2 := by
        linarith [htheta.2, Real.pi_pos]
      have hneg := Real.cos_nonpos_of_pi_div_two_le_of_le hle h2
      linarith
  · exact Real.cos_pos_of_mem_Ioo

private theorem polar_halfDisk_pointwise (F : ℝ → ℝ)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • halfDisk.indicator
        (fun q : ℝ × ℝ =>
          q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
        (polarCoord.symm p) =
      (Set.Iic (1 : ℝ)).indicator
          (fun r => r ^ 2 * F r) p.1 *
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)).indicator
          Real.cos p.2 := by
  rcases p with ⟨r, theta⟩
  have hr : 0 < r := hp.1
  have htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
  have htrig : (r * Real.cos theta) ^ 2 +
      (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hunit :
      r ^ 2 ≤ 1 ↔ r ≤ 1 := by
    constructor
    · intro h
      nlinarith [sq_nonneg (r - 1)]
    · intro h
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h)]
  have hmem :
      polarCoord.symm (r, theta) ∈ halfDisk ↔
        r ≤ 1 ∧ theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [polarCoord_symm_apply]
    simp only [halfDisk, Set.mem_setOf_eq]
    rw [htrig]
    constructor
    · rintro ⟨hcos, hsq⟩
      exact ⟨hunit.mp hsq,
        (cos_pos_iff_in_half htheta).mp
          ((mul_pos_iff_of_pos_left hr).mp hcos)⟩
    · rintro ⟨hr1, ht⟩
      exact ⟨(mul_pos_iff_of_pos_left hr).mpr
          ((cos_pos_iff_in_half htheta).mpr ht),
        hunit.mpr hr1⟩
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases hr1 : r ≤ 1
  · by_cases ht : theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
    · simp only [hr1, ht, and_self, if_true]
      rw [polarCoord_symm_apply, htrig, Real.sqrt_sq_eq_abs,
        abs_of_pos hr]
      ring
    · simp [hr1, ht]
  · simp [hr1]

private theorem radial_unitBall_formula
    (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ p in unitBall,
        F (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))) =
      4 * Real.pi * ∫ r in (0 : ℝ)..1, r ^ 2 * F r := by
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    F (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))
  have hG : Continuous G := by
    exact hF.comp
      (Real.continuous_sqrt.comp
        (((continuous_fst.pow 2).add
          ((continuous_fst.comp continuous_snd).pow 2)).add
          ((continuous_snd.comp continuous_snd).pow 2)))
  have hK : Integrable (unitBall.indicator G) := by
    rw [integrable_indicator_iff unitBall_closed.measurableSet]
    exact hG.continuousOn.integrableOn_compact unitBall_compact
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hK' : Integrable
      (fun q : (ℝ × ℝ) × ℝ => unitBall.indicator G (e q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        e.measurableEmbedding).2 hK
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ, unitBall.indicator G (e q)) =
        ∫ p : ℝ × (ℝ × ℝ), unitBall.indicator G p :=
    volume_preserving_prodAssoc.integral_comp' (unitBall.indicator G)
  rw [← integral_indicator unitBall_closed.measurableSet]
  change (∫ p : ℝ × (ℝ × ℝ), unitBall.indicator G p) = _
  rw [← hreassoc]
  have hFubini :
      (∫ q : (ℝ × ℝ) × ℝ, unitBall.indicator G (e q)) =
        ∫ z : ℝ, ∫ q : ℝ × ℝ,
          unitBall.indicator G (e (q, z)) := by
    exact MeasureTheory.integral_prod_symm
      (fun q : (ℝ × ℝ) × ℝ => unitBall.indicator G (e q)) hK'
  rw [hFubini]
  change (∫ z : ℝ, ∫ q : ℝ × ℝ,
    unitBall.indicator G (q.1, (q.2, z))) = _
  have hxy (z : ℝ) :
      (∫ q : ℝ × ℝ, unitBall.indicator G (q.1, (q.2, z))) =
        (∫ r in Set.Ioi (0 : ℝ),
            unitDisk.indicator
              (fun q : ℝ × ℝ =>
                q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
              (r, z)) *
          (2 * Real.pi) := by
    have hp := integral_comp_polarCoord_symm
      (fun q : ℝ × ℝ => unitBall.indicator G (q.1, (q.2, z)))
    have hprod :
        (∫ p in polarCoord.target,
          p.1 • unitBall.indicator G
            ((polarCoord.symm p).1, ((polarCoord.symm p).2, z))) =
          (∫ r in Set.Ioi (0 : ℝ),
              unitDisk.indicator
                (fun q : ℝ × ℝ =>
                  q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
                (r, z)) *
            ∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [polarCoord_target]
      calc
        _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            unitDisk.indicator
                (fun q : ℝ × ℝ =>
                  q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
                (p.1, z) * (1 : ℝ) := by
          apply setIntegral_congr_fun
            (measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp'
          simpa [G] using polar_xy_pointwise F z p hp'
        _ = _ := by
          exact setIntegral_prod_mul
            (fun r : ℝ =>
              unitDisk.indicator
                (fun q : ℝ × ℝ =>
                  q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
                (r, z))
            (fun _ : ℝ => (1 : ℝ))
            (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
    rw [hprod, angular_full] at hp
    exact hp.symm
  simp_rw [hxy]
  let J : ℝ × ℝ → ℝ := fun q =>
    q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))
  have hhalfMeas : MeasurableSet halfDisk := by
    exact (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const).measurableSet
  have hunitDiskCompact : IsCompact unitDisk := by
    apply (isCompact_Icc :
      IsCompact (Set.Icc ((-1 : ℝ), (-1 : ℝ))
        ((1 : ℝ), (1 : ℝ)))).of_isClosed_subset
    · exact isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const
    · intro q hq
      change q.1 ^ 2 + q.2 ^ 2 ≤ 1 at hq
      have hx : q.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg q.2]
      have hy : q.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg q.1]
      exact ⟨⟨by nlinarith [sq_nonneg (q.1 + 1)],
        by nlinarith [sq_nonneg (q.2 + 1)]⟩,
        ⟨by nlinarith [sq_nonneg (q.1 - 1)],
        by nlinarith [sq_nonneg (q.2 - 1)]⟩⟩
  have hJc : Continuous J := by
    exact continuous_fst.mul
      (hF.comp (Real.continuous_sqrt.comp
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))))
  have hhalfSub : halfDisk ⊆ unitDisk := by
    intro q hq
    exact hq.2
  have hJint : Integrable (halfDisk.indicator J) := by
    rw [integrable_indicator_iff hhalfMeas]
    exact (hJc.continuousOn.integrableOn_compact hunitDiskCompact).mono_set hhalfSub
  have hplane :
      (∫ z : ℝ,
          (∫ r in Set.Ioi (0 : ℝ),
            unitDisk.indicator J (r, z))) =
        ∫ q in halfDisk, J q := by
    rw [← integral_indicator hhalfMeas]
    have hfub :
        (∫ q : ℝ × ℝ, halfDisk.indicator J q) =
          ∫ z : ℝ, ∫ r : ℝ, halfDisk.indicator J (r, z) := by
      exact MeasureTheory.integral_prod_symm
        (halfDisk.indicator J) hJint
    rw [hfub]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with r
    by_cases hr : 0 < r
    · have heq :
          ((r, z) ∈ halfDisk ↔ (r, z) ∈ unitDisk) := by
        simp [halfDisk, unitDisk, hr]
      by_cases hu : (r, z) ∈ unitDisk
      · simp [Set.indicator, hr, hu, heq.mpr hu]
      · have hh : (r, z) ∉ halfDisk := by
          intro h
          exact hu (heq.mp h)
        simp [Set.indicator, hr, hu, hh]
    · have hnot : (r, z) ∉ halfDisk := by
        intro h
        exact hr h.1
      simp [Set.indicator, hr, hnot]
  have hmul :
      (∫ z : ℝ,
        (∫ r in Set.Ioi (0 : ℝ), unitDisk.indicator J (r, z)) *
          (2 * Real.pi)) =
        (∫ z : ℝ,
          ∫ r in Set.Ioi (0 : ℝ), unitDisk.indicator J (r, z)) *
          (2 * Real.pi) := by
    rw [integral_mul_const]
  rw [hmul]
  rw [hplane]
  have hp2 := integral_comp_polarCoord_symm (halfDisk.indicator J)
  rw [integral_indicator hhalfMeas] at hp2
  have hprod2 :
      (∫ p in polarCoord.target,
          p.1 • halfDisk.indicator J (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic (1 : ℝ)).indicator
              (fun r => r ^ 2 * F r) r) *
          ∫ theta in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
            Real.cos theta := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic (1 : ℝ)).indicator
              (fun r => r ^ 2 * F r) p.1 *
            (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)).indicator
              Real.cos p.2 := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        simpa [J] using polar_halfDisk_pointwise F p hp'
      _ = (∫ r in Set.Ioi (0 : ℝ),
              (Set.Iic (1 : ℝ)).indicator
                (fun r => r ^ 2 * F r) r) *
            ∫ theta in Set.Ioo (-Real.pi) Real.pi,
              (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)).indicator
                Real.cos theta := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic (1 : ℝ)).indicator (fun r => r ^ 2 * F r) r)
          (fun theta : ℝ =>
            (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)).indicator
              Real.cos theta)
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
      _ = _ := by
        congr 1
        rw [setIntegral_indicator measurableSet_Ioo]
        have hinter :
            Set.Ioo (-Real.pi) Real.pi ∩
                Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) =
              Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          apply Set.inter_eq_right.mpr
          intro theta htheta
          exact ⟨by linarith [htheta.1, Real.pi_pos],
            by linarith [htheta.2, Real.pi_pos]⟩
        rw [hinter]
  rw [hprod2, angular_half_cos] at hp2
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic (1 : ℝ)).indicator
            (fun r => r ^ 2 * F r) r) =
        ∫ r in (0 : ℝ)..1, r ^ 2 * F r := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic 1 = Set.Ioc (0 : ℝ) 1 := by
      ext r
      simp
    rw [hinter, intervalIntegral.integral_of_le zero_le_one]
  rw [hrad] at hp2
  rw [← hp2]
  ring

private theorem unitBall_volume :
    (∫ _p in unitBall, (1 : ℝ)) = 4 / 3 * Real.pi := by
  have h := radial_unitBall_formula (fun _ : ℝ => (1 : ℝ)) continuous_const
  rw [h]
  rw [show (fun r : ℝ => r ^ 2 * (1 : ℝ)) = fun r => r ^ 2 by
    funext r
    ring]
  rw [integral_pow]
  norm_num
  ring

private theorem ellipsoid_volume (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c = 4 / 3 * Real.pi * a * b * c := by
  unfold volume
  rw [scale_set_integral a b c ha hb hc (fun _ => (1 : ℝ))]
  simp only [mul_one]
  have hconst :
    (∫ _p in unitBall, a * b * c) =
      a * b * c * ∫ _p in unitBall, (1 : ℝ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  rw [hconst, unitBall_volume]
  ring

private theorem ellipsoid_exp_integral (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ p in ellipsoid a b c, radialExponential a b c p) =
      4 * Real.pi * a * b * c *
        ∫ r in (0 : ℝ)..1, r ^ 2 * Real.exp r := by
  rw [scale_set_integral a b c ha hb hc
    (radialExponential a b c)]
  have hpoint (p : ℝ × ℝ × ℝ) :
      a * b * c * radialExponential a b c (scale3 a b c p) =
        a * b * c *
          Real.exp (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) := by
    simp only [radialExponential, scale3_apply]
    have hx : (a * p.1) ^ 2 / a ^ 2 = p.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * p.2.1) ^ 2 / b ^ 2 = p.2.1 ^ 2 := by
      field_simp [hb.ne']
    have hz : (c * p.2.2) ^ 2 / c ^ 2 = p.2.2 ^ 2 := by
      field_simp [hc.ne']
    rw [hx, hy, hz]
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul]
  rw [radial_unitBall_formula Real.exp Real.continuous_exp]
  ring

private theorem radial_exp_integral :
    (∫ r in (0 : ℝ)..1, r ^ 2 * Real.exp r) =
      Real.exp 1 - 2 := by
  let P : ℝ → ℝ := fun r => Real.exp r * (r ^ 2 - 2 * r + 2)
  have hd : ∀ r : ℝ, HasDerivAt P (r ^ 2 * Real.exp r) r := by
    intro r
    dsimp [P]
    convert (Real.hasDerivAt_exp r).mul
      (((hasDerivAt_id r).pow 2).sub
        ((hasDerivAt_id r).const_mul 2) |>.add_const 2) using 1 <;>
      simp <;> ring
  have hc : Continuous (fun r : ℝ => r ^ 2 * Real.exp r) :=
    (continuous_id.pow 2).mul Real.continuous_exp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hd r) (hc.intervalIntegrable 0 1)
  dsimp [P] at h
  simpa using h

private theorem average_value (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    average a b c = 3 * (Real.exp 1 - 2) := by
  unfold average
  rw [ellipsoid_exp_integral a b c ha hb hc,
    ellipsoid_volume a b c ha hb hc, radial_exp_integral]
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne', hc.ne']

theorem gap1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c = 4 / 3 * Real.pi * a * b * c := by
  exact ellipsoid_volume a b c ha hb hc

theorem gap2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    average a b c =
      3 / (4 * Real.pi * a * b * c) *
        ∫ p in ellipsoid a b c, radialExponential a b c p := by
  unfold average
  rw [ellipsoid_volume a b c ha hb hc]
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne', hc.ne']

theorem gap3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    average a b c =
      3 / (4 * Real.pi * a * b * c) * 8 *
        ∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              a * b * c * Real.exp r * r ^ 2 * Real.cos psi := by
  rw [average_value a b c ha hb hc]
  have hr := radial_exp_integral
  have hpsi :
      (∫ psi in (0 : ℝ)..Real.pi / 2, Real.cos psi) = 1 := by
    rw [integral_cos, Real.sin_pi_div_two, Real.sin_zero]
    norm_num
  have hinner (psi : ℝ) :
      (∫ r in (0 : ℝ)..1,
        a * b * c * Real.exp r * r ^ 2 * Real.cos psi) =
        (a * b * c * Real.cos psi) * (Real.exp 1 - 2) := by
    rw [show (fun r : ℝ =>
        a * b * c * Real.exp r * r ^ 2 * Real.cos psi) =
      fun r => (a * b * c * Real.cos psi) * (r ^ 2 * Real.exp r) by
      funext r
      ring]
    rw [intervalIntegral.integral_const_mul, radial_exp_integral]
  simp_rw [hinner]
  have hmiddle :
      (∫ psi in (0 : ℝ)..Real.pi / 2,
        (a * b * c * Real.cos psi) * (Real.exp 1 - 2)) =
        a * b * c * (Real.exp 1 - 2) := by
    rw [show (fun psi : ℝ =>
        (a * b * c * Real.cos psi) * (Real.exp 1 - 2)) =
      fun psi => (a * b * c * (Real.exp 1 - 2)) * Real.cos psi by
        funext psi
        ring]
    rw [intervalIntegral.integral_const_mul, hpsi, mul_one]
  rw [hmiddle]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne', hc.ne']
  ring

theorem gap4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    average a b c =
      3 * (∫ psi in (0 : ℝ)..Real.pi / 2, Real.cos psi) *
        ∫ r in (0 : ℝ)..1, r ^ 2 * Real.exp r := by
  rw [average_value a b c ha hb hc, radial_exp_integral]
  rw [integral_cos, Real.sin_pi_div_two, Real.sin_zero]
  norm_num

theorem gap5 :
    3 * (∫ psi in (0 : ℝ)..Real.pi / 2, Real.cos psi) *
        (∫ r in (0 : ℝ)..1, r ^ 2 * Real.exp r) =
      3 * (Real.exp 1 - 2) := by
  rw [radial_exp_integral, integral_cos,
    Real.sin_pi_div_two, Real.sin_zero]
  norm_num

theorem gap6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    average a b c = 3 * (Real.exp 1 - 2) := by
  exact average_value a b c ha hb hc

end

end ProofGap.Exercise4095
