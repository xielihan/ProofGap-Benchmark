import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4079

noncomputable section

open MeasureTheory
open scoped Interval

def ellipsoid (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 +
    p.2.2 ^ 2 / c ^ 2 ≤ 1}

def normalizedRadiusSq (a b c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 +
    p.2.2 ^ 2 / c ^ 2

def ellipsoidIntegral (a b c : ℝ) : ℝ :=
  ∫ p in ellipsoid a b c, normalizedRadiusSq a b c p

def sectionX (a b c x : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 / b ^ 2 + p.2 ^ 2 / c ^ 2 ≤
    1 - x ^ 2 / a ^ 2}

def sectionY (a b c y : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 / c ^ 2 + p.2 ^ 2 / a ^ 2 ≤
    1 - y ^ 2 / b ^ 2}

def sectionZ (a b c z : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤
    1 - z ^ 2 / c ^ 2}

def sectionArea (s : Set (ℝ × ℝ)) : ℝ :=
  ∫ _ in s, (1 : ℝ)

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

private theorem unitBall_radiusSq_integral :
    (∫ p in unitBall, p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) =
      4 * Real.pi / 5 := by
  have h := radial_unitBall_formula (fun r : ℝ => r ^ 2)
    (continuous_id.pow 2)
  have hleft :
      (∫ p in unitBall,
          (Real.sqrt
            (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) ^ 2) =
        ∫ p in unitBall, p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
    apply setIntegral_congr_fun unitBall_closed.measurableSet
    intro p hp
    change
      Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 2 =
        p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2
    rw [Real.sq_sqrt]
    positivity
  rw [hleft] at h
  rw [show (fun r : ℝ => r ^ 2 * r ^ 2) = fun r => r ^ 4 by
    funext r
    ring, integral_pow] at h
  norm_num at h
  nlinarith [h]

private theorem ellipsoidIntegral_value (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ellipsoidIntegral a b c = 4 * Real.pi * a * b * c / 5 := by
  unfold ellipsoidIntegral
  rw [scale_set_integral a b c ha hb hc
    (normalizedRadiusSq a b c)]
  have hpoint (p : ℝ × ℝ × ℝ) :
      a * b * c * normalizedRadiusSq a b c (scale3 a b c p) =
        a * b * c * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
    simp only [normalizedRadiusSq, scale3_apply]
    have hx : (a * p.1) ^ 2 / a ^ 2 = p.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * p.2.1) ^ 2 / b ^ 2 = p.2.1 ^ 2 := by
      field_simp [hb.ne']
    have hz : (c * p.2.2) ^ 2 / c ^ 2 = p.2.2 ^ 2 := by
      field_simp [hc.ne']
    rw [hx, hy, hz]
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul, unitBall_radiusSq_integral]
  ring

private theorem unitDisk_closed : IsClosed unitDisk := by
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem disk_polar_pointwise (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    p.1 • unitDisk.indicator (fun _q : ℝ × ℝ => (1 : ℝ))
        (polarCoord.symm p) =
      (Set.Iic (1 : ℝ)).indicator (fun r => r) p.1 * (1 : ℝ) := by
  rcases p with ⟨r, theta⟩
  have hr : 0 < r := hp.1
  have htrig :
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem : polarCoord.symm (r, theta) ∈ unitDisk ↔ r ≤ 1 := by
    rw [polarCoord_symm_apply]
    simp only [unitDisk, Set.mem_setOf_eq]
    rw [htrig]
    constructor
    · intro h
      nlinarith [sq_nonneg (r - 1)]
    · intro h
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h)]
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases h : r ≤ 1 <;> simp [h]

private theorem unitDisk_area :
    (∫ _q in unitDisk, (1 : ℝ)) = Real.pi := by
  have hp := integral_comp_polarCoord_symm
    (unitDisk.indicator (fun _q : ℝ × ℝ => (1 : ℝ)))
  rw [integral_indicator unitDisk_closed.measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • unitDisk.indicator (fun _q : ℝ × ℝ => (1 : ℝ))
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic (1 : ℝ)).indicator (fun r => r) r) *
          ∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic (1 : ℝ)).indicator (fun r => r) p.1 *
            (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact disk_polar_pointwise p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ => (Set.Iic (1 : ℝ)).indicator (fun r => r) r)
          (fun _theta : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic (1 : ℝ)).indicator (fun r => r) r) = 1 / 2 := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic 1 = Set.Ioc (0 : ℝ) 1 := by
      ext r
      simp
    rw [hinter]
    calc
      (∫ r in Set.Ioc (0 : ℝ) 1, r) =
          ∫ r in (0 : ℝ)..1, r := by
        rw [intervalIntegral.integral_of_le zero_le_one]
      _ = 1 / 2 := by
        rw [integral_id]
        norm_num
  rw [hprod, hrad, angular_full] at hp
  nlinarith [hp]

private def ellipse2 (d e : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 / d ^ 2 + q.2 ^ 2 / e ^ 2 ≤ 1}

private def scale2 (d e : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (scale1 d).prodMap (scale1 e)

@[simp] private theorem scale2_apply (d e : ℝ) (q : ℝ × ℝ) :
    scale2 d e q = (d * q.1, e * q.2) := by
  rcases q with ⟨x, y⟩
  simp [scale2]

private theorem det_scale2 (d e : ℝ) :
    (scale2 d e).det = d * e := by
  unfold scale2
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap,
    LinearMap.det_prodMap]
  change (scale1 d).det * (scale1 e).det = _
  rw [det_scale1, det_scale1]

private theorem scale2_image_unitDisk (d e : ℝ)
    (hd : 0 < d) (he : 0 < e) :
    scale2 d e '' unitDisk = ellipse2 d e := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hx : (d * p.1) ^ 2 / d ^ 2 = p.1 ^ 2 := by
      field_simp [hd.ne']
    have hy : (e * p.2) ^ 2 / e ^ 2 = p.2 ^ 2 := by
      field_simp [he.ne']
    simpa [unitDisk, ellipse2, hx, hy] using hp
  · intro hq
    let p : ℝ × ℝ := (q.1 / d, q.2 / e)
    have hmap : scale2 d e p = q := by
      rw [scale2_apply]
      apply Prod.ext
      · dsimp [p]
        field_simp [hd.ne']
      · dsimp [p]
        field_simp [he.ne']
    refine ⟨p, ?_, hmap⟩
    have hx : (q.1 / d) ^ 2 = q.1 ^ 2 / d ^ 2 := by ring
    have hy : (q.2 / e) ^ 2 = q.2 ^ 2 / e ^ 2 := by ring
    simpa [unitDisk, ellipse2, p, hx, hy] using hq

private theorem scale2_injOn (d e : ℝ)
    (hd : 0 < d) (he : 0 < e) :
    Set.InjOn (scale2 d e) unitDisk := by
  intro p hp q hq heq
  have h1 : d * p.1 = d * q.1 := by
    simpa using congrArg Prod.fst heq
  have h2 : e * p.2 = e * q.2 := by
    simpa using congrArg Prod.snd heq
  apply Prod.ext
  · exact mul_left_cancel₀ hd.ne' h1
  · exact mul_left_cancel₀ he.ne' h2

private theorem ellipse2_area (d e : ℝ)
    (hd : 0 < d) (he : 0 < e) :
    (∫ _q in ellipse2 d e, (1 : ℝ)) = Real.pi * d * e := by
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) unitDisk_closed.measurableSet
      (f := scale2 d e) (f' := fun _ => scale2 d e)
      (fun q hq => (scale2 d e).hasFDerivAt.hasFDerivWithinAt)
      (scale2_injOn d e hd he) (fun _q : ℝ × ℝ => (1 : ℝ))
  rw [scale2_image_unitDisk d e hd he] at hchange
  have hde : 0 < d * e := mul_pos hd he
  simp only [det_scale2, abs_of_pos hde, smul_eq_mul, mul_one] at hchange
  have hconst :
      (∫ _q in unitDisk, d * e) =
        d * e * ∫ _q in unitDisk, (1 : ℝ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with q
    ring
  rw [hconst, unitDisk_area] at hchange
  nlinarith [hchange]

private def sectionEllipse (d e t : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 / d ^ 2 + q.2 ^ 2 / e ^ 2 ≤ t}

private theorem sectionEllipse_area (d e t : ℝ)
    (hd : 0 < d) (he : 0 < e) (ht : 0 ≤ t) :
    (∫ _q in sectionEllipse d e t, (1 : ℝ)) =
      Real.pi * d * e * t := by
  by_cases ht0 : t = 0
  · subst t
    have hset : sectionEllipse d e 0 = {(0, 0)} := by
      ext q
      constructor
      · intro hq
        change q.1 ^ 2 / d ^ 2 + q.2 ^ 2 / e ^ 2 ≤ 0 at hq
        have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
        have he2 : 0 < e ^ 2 := sq_pos_of_pos he
        have hx : 0 ≤ q.1 ^ 2 / d ^ 2 :=
          div_nonneg (sq_nonneg q.1) hd2.le
        have hy : 0 ≤ q.2 ^ 2 / e ^ 2 :=
          div_nonneg (sq_nonneg q.2) he2.le
        have hx0 : q.1 = 0 := by
          have : q.1 ^ 2 / d ^ 2 = 0 := by nlinarith
          have : q.1 ^ 2 = 0 := (div_eq_zero_iff).mp this |>.resolve_right hd2.ne'
          nlinarith
        have hy0 : q.2 = 0 := by
          have : q.2 ^ 2 / e ^ 2 = 0 := by nlinarith
          have : q.2 ^ 2 = 0 := (div_eq_zero_iff).mp this |>.resolve_right he2.ne'
          nlinarith
        exact Prod.ext hx0 hy0
      · intro hq
        have hq0 : q = (0, 0) := by simpa using hq
        subst q
        norm_num [sectionEllipse]
    rw [hset]
    simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let D := d * Real.sqrt t
    let E := e * Real.sqrt t
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
    have hD : 0 < D := mul_pos hd hsqrt
    have hE : 0 < E := mul_pos he hsqrt
    have hset : sectionEllipse d e t = ellipse2 D E := by
      ext q
      change
        q.1 ^ 2 / d ^ 2 + q.2 ^ 2 / e ^ 2 ≤ t ↔
          q.1 ^ 2 / D ^ 2 + q.2 ^ 2 / E ^ 2 ≤ 1
      have hsq : (Real.sqrt t) ^ 2 = t :=
        Real.sq_sqrt ht
      have heq :
          q.1 ^ 2 / D ^ 2 + q.2 ^ 2 / E ^ 2 =
            (q.1 ^ 2 / d ^ 2 + q.2 ^ 2 / e ^ 2) / t := by
        dsimp [D, E]
        field_simp [hd.ne', he.ne', htpos.ne']
        rw [hsq]
        ring
      rw [heq]
      exact (div_le_one htpos).symm
    rw [hset, ellipse2_area D E hD hE]
    dsimp [D, E]
    calc
      Real.pi * (d * Real.sqrt t) * (e * Real.sqrt t) =
          Real.pi * d * e * (Real.sqrt t) ^ 2 := by ring
      _ = Real.pi * d * e * t := by rw [Real.sq_sqrt ht]

private theorem sectionX_area_value (a b c x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : x ∈ Set.Icc (-a) a) :
    sectionArea (sectionX a b c x) =
      Real.pi * b * c * (1 - x ^ 2 / a ^ 2) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hx2 : x ^ 2 ≤ a ^ 2 := by
    have hprod : 0 ≤ (a - x) * (a + x) :=
      mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1])
    nlinarith
  have ht : 0 ≤ 1 - x ^ 2 / a ^ 2 := by
    have := (div_le_one ha2).2 hx2
    linarith
  unfold sectionArea
  change
    (∫ _q in sectionEllipse b c (1 - x ^ 2 / a ^ 2), (1 : ℝ)) =
      _
  exact sectionEllipse_area b c (1 - x ^ 2 / a ^ 2) hb hc ht

private theorem sectionY_area_value (a b c y : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hy : y ∈ Set.Icc (-b) b) :
    sectionArea (sectionY a b c y) =
      Real.pi * a * c * (1 - y ^ 2 / b ^ 2) := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hy2 : y ^ 2 ≤ b ^ 2 := by
    have hprod : 0 ≤ (b - y) * (b + y) :=
      mul_nonneg (sub_nonneg.mpr hy.2) (by linarith [hy.1])
    nlinarith
  have ht : 0 ≤ 1 - y ^ 2 / b ^ 2 := by
    have := (div_le_one hb2).2 hy2
    linarith
  unfold sectionArea
  change
    (∫ _q in sectionEllipse c a (1 - y ^ 2 / b ^ 2), (1 : ℝ)) =
      _
  rw [sectionEllipse_area c a (1 - y ^ 2 / b ^ 2) hc ha ht]
  ring

private theorem sectionZ_area_value (a b c z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hz : z ∈ Set.Icc (-c) c) :
    sectionArea (sectionZ a b c z) =
      Real.pi * a * b * (1 - z ^ 2 / c ^ 2) := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hz2 : z ^ 2 ≤ c ^ 2 := by
    have hprod : 0 ≤ (c - z) * (c + z) :=
      mul_nonneg (sub_nonneg.mpr hz.2) (by linarith [hz.1])
    nlinarith
  have ht : 0 ≤ 1 - z ^ 2 / c ^ 2 := by
    have := (div_le_one hc2).2 hz2
    linarith
  unfold sectionArea
  change
    (∫ _q in sectionEllipse a b (1 - z ^ 2 / c ^ 2), (1 : ℝ)) =
      _
  exact sectionEllipse_area a b (1 - z ^ 2 / c ^ 2) ha hb ht

private theorem axis_moment (d : ℝ) (hd : 0 < d) :
    (∫ x in -d..d, x ^ 2 * (1 - x ^ 2 / d ^ 2)) =
      4 * d ^ 3 / 15 := by
  have h2 : IntervalIntegrable (fun x : ℝ => x ^ 2)
      MeasureTheory.volume (-d) d :=
    (continuous_id.pow 2).intervalIntegrable
      (μ := MeasureTheory.volume) (-d) d
  have h4 : IntervalIntegrable (fun x : ℝ => x ^ 4)
      MeasureTheory.volume (-d) d :=
    (continuous_id.pow 4).intervalIntegrable
      (μ := MeasureTheory.volume) (-d) d
  have hfun :
      (fun x : ℝ => x ^ 2 * (1 - x ^ 2 / d ^ 2)) =
        fun x => x ^ 2 - (1 / d ^ 2) * x ^ 4 := by
    funext x
    field_simp [hd.ne']
  rw [hfun]
  rw [intervalIntegral.integral_sub h2
      (h4.const_mul (1 / d ^ 2)),
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  field_simp [hd.ne']
  ring

private theorem sliceX_moment (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ x in -a..a,
      x ^ 2 / a ^ 2 * sectionArea (sectionX a b c x)) =
      4 * Real.pi * a * b * c / 15 := by
  have hcongr :
      (∫ x in -a..a,
        x ^ 2 / a ^ 2 * sectionArea (sectionX a b c x)) =
        ∫ x in -a..a,
          x ^ 2 / a ^ 2 *
            (Real.pi * b * c * (1 - x ^ 2 / a ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (-a) a := by
      simpa [Set.uIcc_of_le (neg_le_self ha.le)] using hx
    change
      x ^ 2 / a ^ 2 * sectionArea (sectionX a b c x) =
        x ^ 2 / a ^ 2 *
          (Real.pi * b * c * (1 - x ^ 2 / a ^ 2))
    rw [sectionX_area_value a b c x ha hb hc hx']
  rw [hcongr]
  rw [show (fun x : ℝ =>
      x ^ 2 / a ^ 2 *
        (Real.pi * b * c * (1 - x ^ 2 / a ^ 2))) =
      fun x => (Real.pi * b * c / a ^ 2) *
        (x ^ 2 * (1 - x ^ 2 / a ^ 2)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul, axis_moment a ha]
  field_simp [ha.ne']

private theorem sliceY_moment (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ y in -b..b,
      y ^ 2 / b ^ 2 * sectionArea (sectionY a b c y)) =
      4 * Real.pi * a * b * c / 15 := by
  have hcongr :
      (∫ y in -b..b,
        y ^ 2 / b ^ 2 * sectionArea (sectionY a b c y)) =
        ∫ y in -b..b,
          y ^ 2 / b ^ 2 *
            (Real.pi * a * c * (1 - y ^ 2 / b ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Set.Icc (-b) b := by
      simpa [Set.uIcc_of_le (neg_le_self hb.le)] using hy
    change
      y ^ 2 / b ^ 2 * sectionArea (sectionY a b c y) =
        y ^ 2 / b ^ 2 *
          (Real.pi * a * c * (1 - y ^ 2 / b ^ 2))
    rw [sectionY_area_value a b c y ha hb hc hy']
  rw [hcongr]
  rw [show (fun y : ℝ =>
      y ^ 2 / b ^ 2 *
        (Real.pi * a * c * (1 - y ^ 2 / b ^ 2))) =
      fun y => (Real.pi * a * c / b ^ 2) *
        (y ^ 2 * (1 - y ^ 2 / b ^ 2)) by
    funext y
    ring]
  rw [intervalIntegral.integral_const_mul, axis_moment b hb]
  field_simp [hb.ne']

private theorem sliceZ_moment (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ z in -c..c,
      z ^ 2 / c ^ 2 * sectionArea (sectionZ a b c z)) =
      4 * Real.pi * a * b * c / 15 := by
  have hcongr :
      (∫ z in -c..c,
        z ^ 2 / c ^ 2 * sectionArea (sectionZ a b c z)) =
        ∫ z in -c..c,
          z ^ 2 / c ^ 2 *
            (Real.pi * a * b * (1 - z ^ 2 / c ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Set.Icc (-c) c := by
      simpa [Set.uIcc_of_le (neg_le_self hc.le)] using hz
    change
      z ^ 2 / c ^ 2 * sectionArea (sectionZ a b c z) =
        z ^ 2 / c ^ 2 *
          (Real.pi * a * b * (1 - z ^ 2 / c ^ 2))
    rw [sectionZ_area_value a b c z ha hb hc hz']
  rw [hcongr]
  rw [show (fun z : ℝ =>
      z ^ 2 / c ^ 2 *
        (Real.pi * a * b * (1 - z ^ 2 / c ^ 2))) =
      fun z => (Real.pi * a * b / c ^ 2) *
        (z ^ 2 * (1 - z ^ 2 / c ^ 2)) by
    funext z
    ring]
  rw [intervalIntegral.integral_const_mul, axis_moment c hc]
  field_simp [hc.ne']

theorem gap1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ellipsoidIntegral a b c =
      (∫ x in -a..a, x ^ 2 / a ^ 2 * sectionArea (sectionX a b c x)) +
      (∫ y in -b..b, y ^ 2 / b ^ 2 * sectionArea (sectionY a b c y)) +
      ∫ z in -c..c, z ^ 2 / c ^ 2 * sectionArea (sectionZ a b c z) := by
  rw [ellipsoidIntegral_value a b c ha hb hc,
    sliceX_moment a b c ha hb hc,
    sliceY_moment a b c ha hb hc,
    sliceZ_moment a b c ha hb hc]
  ring

theorem gap2 (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : x ∈ Set.Icc (-a) a) :
    sectionArea (sectionX a b c x) =
      Real.pi * b * c * (1 - x ^ 2 / a ^ 2) := by
  exact sectionX_area_value a b c x ha hb hc hx

theorem gap3 (a b c y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hy : y ∈ Set.Icc (-b) b) :
    sectionArea (sectionY a b c y) =
      Real.pi * a * c * (1 - y ^ 2 / b ^ 2) := by
  exact sectionY_area_value a b c y ha hb hc hy

theorem gap4 (a b c z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hz : z ∈ Set.Icc (-c) c) :
    sectionArea (sectionZ a b c z) =
      Real.pi * a * b * (1 - z ^ 2 / c ^ 2) := by
  exact sectionZ_area_value a b c z ha hb hc hz

theorem gap5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ellipsoidIntegral a b c =
      Real.pi * b * c / a ^ 2 *
          (∫ x in -a..a, x ^ 2 * (1 - x ^ 2 / a ^ 2)) +
        Real.pi * a * c / b ^ 2 *
          (∫ y in -b..b, y ^ 2 * (1 - y ^ 2 / b ^ 2)) +
        Real.pi * a * b / c ^ 2 *
          (∫ z in -c..c, z ^ 2 * (1 - z ^ 2 / c ^ 2)) := by
  rw [ellipsoidIntegral_value a b c ha hb hc,
    axis_moment a ha, axis_moment b hb, axis_moment c hc]
  field_simp [ha.ne', hb.ne', hc.ne']
  ring

theorem gap6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ellipsoidIntegral a b c =
      3 * (4 * Real.pi * a * b * c / 15) := by
  rw [ellipsoidIntegral_value a b c ha hb hc]
  ring

theorem gap7 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ellipsoidIntegral a b c =
      4 * Real.pi * a * b * c / 5 := by
  exact ellipsoidIntegral_value a b c ha hb hc

end

end ProofGap.Exercise4079
