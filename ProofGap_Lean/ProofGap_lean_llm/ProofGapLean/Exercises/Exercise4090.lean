import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4090

noncomputable section

open MeasureTheory
open scoped Interval

def ellipsoid (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 +
    p.2.2 ^ 2 / c ^ 2 ≤ 1}

def ellipsoidMap (a b c r phi psi : ℝ) : ℝ × ℝ × ℝ :=
  (a * r * Real.cos phi * Real.cos psi,
    b * r * Real.sin phi * Real.cos psi,
    c * r * Real.sin psi)

def octantParameters : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ Real.pi / 2 ∧
    0 ≤ p.2.1 ∧ p.2.1 ≤ Real.pi / 2 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ 1}

def firstOctant (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  ellipsoid a b c ∩ {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}

def jacobianAbs (a b c r psi : ℝ) : ℝ :=
  |a * b * c * r ^ 2 * Real.cos psi|

def weightedIntegral (a b c : ℝ) : ℝ :=
  ∫ p in ellipsoid a b c,
    Real.sqrt
      (1 - p.1 ^ 2 / a ^ 2 - p.2.1 ^ 2 / b ^ 2 -
        p.2.2 ^ 2 / c ^ 2)

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
    exact (hJc.continuousOn.integrableOn_compact hunitDiskCompact).mono_set
      hhalfSub
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

private theorem radial_trig_integral :
    (∫ r in (0 : ℝ)..1, r ^ 2 * Real.sqrt (1 - r ^ 2)) =
      ∫ t in (0 : ℝ)..Real.pi / 2,
        Real.sin t ^ 2 * Real.cos t ^ 2 := by
  have hsub :
      (∫ t in (0 : ℝ)..Real.pi / 2,
          (Real.sin t ^ 2 *
            Real.sqrt (1 - Real.sin t ^ 2)) *
            Real.cos t) =
        ∫ r in Real.sin 0..Real.sin (Real.pi / 2),
          r ^ 2 * Real.sqrt (1 - r ^ 2) := by
    have hderiv :
        ∀ t ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
          HasDerivAt Real.sin (Real.cos t) t := by
      intro t _
      exact Real.hasDerivAt_sin t
    have hcos : Continuous Real.cos := Real.continuous_cos
    have hintegrand : Continuous
        (fun r : ℝ => r ^ 2 * Real.sqrt (1 - r ^ 2)) :=
      (continuous_id.pow 2).mul
        ((continuous_const.sub (continuous_id.pow 2)).sqrt)
    simpa only [Function.comp_apply] using
      (intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := Real.pi / 2)
        (f := Real.sin) (f' := Real.cos)
        (g := fun r : ℝ => r ^ 2 * Real.sqrt (1 - r ^ 2))
        hderiv hcos.continuousOn hintegrand)
  calc
    (∫ r in (0 : ℝ)..1, r ^ 2 * Real.sqrt (1 - r ^ 2)) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          (Real.sin t ^ 2 *
            Real.sqrt (1 - Real.sin t ^ 2)) *
            Real.cos t := by
      simpa using hsub.symm
    _ = ∫ t in (0 : ℝ)..Real.pi / 2,
        Real.sin t ^ 2 * Real.cos t ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        simpa [Set.uIcc_of_le
          (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using ht
      have hcos : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [ht'.1, Real.pi_pos], ht'.2⟩
      have hsquare :
          1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq t]
      change Real.sin t ^ 2 * Real.sqrt (1 - Real.sin t ^ 2) *
          Real.cos t =
        Real.sin t ^ 2 * Real.cos t ^ 2
      rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hcos]
      ring

private theorem weighted_radial_formula (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    weightedIntegral a b c =
      4 * Real.pi *
        ∫ r in (0 : ℝ)..1,
          a * b * c * r ^ 2 * Real.sqrt (1 - r ^ 2) := by
  unfold weightedIntegral
  rw [scale_set_integral a b c ha hb hc]
  have hpoint (p : ℝ × ℝ × ℝ) :
      a * b * c *
          Real.sqrt
            (1 - (scale3 a b c p).1 ^ 2 / a ^ 2 -
              (scale3 a b c p).2.1 ^ 2 / b ^ 2 -
              (scale3 a b c p).2.2 ^ 2 / c ^ 2) =
        a * b * c *
          Real.sqrt
            (1 - p.1 ^ 2 - p.2.1 ^ 2 - p.2.2 ^ 2) := by
    simp only [scale3_apply]
    have hx : (a * p.1) ^ 2 / a ^ 2 = p.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * p.2.1) ^ 2 / b ^ 2 = p.2.1 ^ 2 := by
      field_simp [hb.ne']
    have hz : (c * p.2.2) ^ 2 / c ^ 2 = p.2.2 ^ 2 := by
      field_simp [hc.ne']
    rw [hx, hy, hz]
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul]
  have hsame :
      (∫ p in unitBall,
          Real.sqrt
            (1 - p.1 ^ 2 - p.2.1 ^ 2 - p.2.2 ^ 2)) =
        ∫ p in unitBall,
          (fun r : ℝ => Real.sqrt (1 - r ^ 2))
            (Real.sqrt
              (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) := by
    apply setIntegral_congr_fun unitBall_closed.measurableSet
    intro p hp
    have hsum :
        0 ≤ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
      positivity
    change Real.sqrt
        (1 - p.1 ^ 2 - p.2.1 ^ 2 - p.2.2 ^ 2) =
      Real.sqrt
        (1 - Real.sqrt
          (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 2)
    rw [Real.sq_sqrt hsum]
    congr 1
    ring
  rw [hsame]
  rw [radial_unitBall_formula
    (fun r : ℝ => Real.sqrt (1 - r ^ 2))
    (by fun_prop)]
  rw [show (fun r : ℝ =>
      a * b * c * r ^ 2 * Real.sqrt (1 - r ^ 2)) =
    fun r => (a * b * c) *
      (r ^ 2 * Real.sqrt (1 - r ^ 2)) by
    funext r
    ring]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem coordinate_integral_formula (a b c : ℝ) :
    8 *
        (∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              a * b * c * r ^ 2 * Real.cos psi *
                Real.sqrt (1 - r ^ 2)) =
      4 * Real.pi *
        ∫ r in (0 : ℝ)..1,
          a * b * c * r ^ 2 * Real.sqrt (1 - r ^ 2) := by
  let R : ℝ :=
    ∫ r in (0 : ℝ)..1,
      a * b * c * r ^ 2 * Real.sqrt (1 - r ^ 2)
  have hr (psi : ℝ) :
      (∫ r in (0 : ℝ)..1,
        a * b * c * r ^ 2 * Real.cos psi *
          Real.sqrt (1 - r ^ 2)) =
        Real.cos psi * R := by
    rw [show (fun r : ℝ =>
        a * b * c * r ^ 2 * Real.cos psi *
          Real.sqrt (1 - r ^ 2)) =
      fun r => Real.cos psi *
        (a * b * c * r ^ 2 * Real.sqrt (1 - r ^ 2)) by
      funext r
      ring]
    rw [intervalIntegral.integral_const_mul]
  simp_rw [hr]
  rw [intervalIntegral.integral_mul_const, integral_cos,
    Real.sin_pi_div_two, Real.sin_zero]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  dsimp [R]
  ring

theorem gap1 (a b c r psi : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : 0 ≤ r) (hpsi₀ : 0 ≤ psi) (hpsi₁ : psi ≤ Real.pi / 2) :
    jacobianAbs a b c r psi =
      a * b * c * r ^ 2 * Real.cos psi := by
  unfold jacobianAbs
  rw [abs_of_nonneg]
  have hcos : 0 ≤ Real.cos psi :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hpsi₀, Real.pi_pos], hpsi₁⟩
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg ha.le hb.le) hc.le)
      (sq_nonneg r)) hcos

theorem gap2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (fun p => ellipsoidMap a b c p.2.2 p.1 p.2.1) '' octantParameters =
      firstOctant a b c := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨phi, psi, r⟩
    change 0 ≤ phi ∧ phi ≤ Real.pi / 2 ∧
      0 ≤ psi ∧ psi ≤ Real.pi / 2 ∧
      0 ≤ r ∧ r ≤ 1 at hp
    have hcosphi : 0 ≤ Real.cos phi :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hp.1, Real.pi_pos], hp.2.1⟩
    have hsinphi : 0 ≤ Real.sin phi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hp.1
        (by linarith [hp.2.1, Real.pi_pos])
    have hcospsi : 0 ≤ Real.cos psi :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hp.2.2.1, Real.pi_pos], hp.2.2.2.1⟩
    have hsinpsi : 0 ≤ Real.sin psi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hp.2.2.1
        (by linarith [hp.2.2.2.1, Real.pi_pos])
    have hx :
        (a * r * Real.cos phi * Real.cos psi) ^ 2 / a ^ 2 =
          r ^ 2 * Real.cos phi ^ 2 * Real.cos psi ^ 2 := by
      field_simp [ha.ne']
    have hy :
        (b * r * Real.sin phi * Real.cos psi) ^ 2 / b ^ 2 =
          r ^ 2 * Real.sin phi ^ 2 * Real.cos psi ^ 2 := by
      field_simp [hb.ne']
    have hz :
        (c * r * Real.sin psi) ^ 2 / c ^ 2 =
          r ^ 2 * Real.sin psi ^ 2 := by
      field_simp [hc.ne']
    constructor
    · change
        (a * r * Real.cos phi * Real.cos psi) ^ 2 / a ^ 2 +
            (b * r * Real.sin phi * Real.cos psi) ^ 2 / b ^ 2 +
            (c * r * Real.sin psi) ^ 2 / c ^ 2 ≤ 1
      rw [hx, hy, hz]
      have hphi := Real.cos_sq_add_sin_sq phi
      have hpsi := Real.cos_sq_add_sin_sq psi
      have hr2 : r ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hp.2.2.2.2.1
          (sub_nonneg.mpr hp.2.2.2.2.2)]
      calc
        r ^ 2 * Real.cos phi ^ 2 * Real.cos psi ^ 2 +
              r ^ 2 * Real.sin phi ^ 2 * Real.cos psi ^ 2 +
              r ^ 2 * Real.sin psi ^ 2 =
            r ^ 2 *
              ((Real.cos phi ^ 2 + Real.sin phi ^ 2) *
                Real.cos psi ^ 2 + Real.sin psi ^ 2) := by ring
        _ = r ^ 2 *
              (Real.cos psi ^ 2 + Real.sin psi ^ 2) := by
          rw [hphi]
          ring
        _ = r ^ 2 := by rw [hpsi]; ring
        _ ≤ 1 := hr2
    · exact ⟨mul_nonneg
          (mul_nonneg (mul_nonneg ha.le hp.2.2.2.2.1) hcosphi)
          hcospsi,
        mul_nonneg
          (mul_nonneg (mul_nonneg hb.le hp.2.2.2.2.1) hsinphi)
          hcospsi,
        mul_nonneg (mul_nonneg hc.le hp.2.2.2.2.1) hsinpsi⟩
  · intro hq
    rcases q with ⟨x, y, z⟩
    change
      (x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 ≤ 1) ∧
        0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z at hq
    let X : ℝ := x / a
    let Y : ℝ := y / b
    let Z : ℝ := z / c
    have hX : 0 ≤ X := by
      dsimp [X]
      exact div_nonneg hq.2.1 ha.le
    have hY : 0 ≤ Y := by
      dsimp [Y]
      exact div_nonneg hq.2.2.1 hb.le
    have hZ : 0 ≤ Z := by
      dsimp [Z]
      exact div_nonneg hq.2.2.2 hc.le
    have hsum :
        X ^ 2 + Y ^ 2 + Z ^ 2 ≤ 1 := by
      dsimp [X, Y, Z]
      convert hq.1 using 1 <;> ring
    let rho : ℝ := Real.sqrt (X ^ 2 + Y ^ 2)
    let r : ℝ := Real.sqrt (X ^ 2 + Y ^ 2 + Z ^ 2)
    have hrho0 : 0 ≤ rho := Real.sqrt_nonneg _
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrhosq : rho ^ 2 = X ^ 2 + Y ^ 2 := by
      dsimp [rho]
      rw [Real.sq_sqrt]
      positivity
    have hrsq : r ^ 2 = X ^ 2 + Y ^ 2 + Z ^ 2 := by
      dsimp [r]
      rw [Real.sq_sqrt]
      positivity
    have hr1 : r ≤ 1 := by
      dsimp [r]
      rw [Real.sqrt_le_one]
      exact hsum
    by_cases hre : r = 0
    · have hsum0 : X ^ 2 + Y ^ 2 + Z ^ 2 = 0 := by
        rw [← hrsq, hre]
        norm_num
      have hXsq : X ^ 2 = 0 := by
        nlinarith [sq_nonneg Y, sq_nonneg Z]
      have hYsq : Y ^ 2 = 0 := by
        nlinarith [sq_nonneg X, sq_nonneg Z]
      have hZsq : Z ^ 2 = 0 := by
        nlinarith [sq_nonneg X, sq_nonneg Y]
      have hXe : X = 0 := by
        exact sq_eq_zero_iff.mp hXsq
      have hYe : Y = 0 := by
        exact sq_eq_zero_iff.mp hYsq
      have hZe : Z = 0 := by
        exact sq_eq_zero_iff.mp hZsq
      have hxe : x = 0 := by
        dsimp [X] at hXe
        simpa [ha.ne'] using hXe
      have hye : y = 0 := by
        dsimp [Y] at hYe
        simpa [hb.ne'] using hYe
      have hze : z = 0 := by
        dsimp [Z] at hZe
        simpa [hc.ne'] using hZe
      refine ⟨((0 : ℝ), ((0 : ℝ), (0 : ℝ))), ?_, ?_⟩
      · change 0 ≤ (0 : ℝ) ∧ 0 ≤ Real.pi / 2 ∧
          0 ≤ (0 : ℝ) ∧ 0 ≤ Real.pi / 2 ∧
          0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1
        norm_num
        positivity
      · simp [ellipsoidMap, hxe, hye, hze]
    · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hre)
      by_cases hrhoe : rho = 0
      · have hXY0 : X ^ 2 + Y ^ 2 = 0 := by
          rw [← hrhosq, hrhoe]
          norm_num
        have hXYsq : X ^ 2 = 0 ∧ Y ^ 2 = 0 :=
          (add_eq_zero_iff_of_nonneg
            (sq_nonneg X) (sq_nonneg Y)).mp hXY0
        have hXsq : X ^ 2 = 0 := hXYsq.1
        have hYsq : Y ^ 2 = 0 := hXYsq.2
        have hXe : X = 0 := sq_eq_zero_iff.mp hXsq
        have hYe : Y = 0 := sq_eq_zero_iff.mp hYsq
        have hxe : x = 0 := by
          dsimp [X] at hXe
          simpa [ha.ne'] using hXe
        have hye : y = 0 := by
          dsimp [Y] at hYe
          simpa [hb.ne'] using hYe
        have hrZ : r = Z := by
          apply (sq_eq_sq₀ hr0 hZ).mp
          rw [hrsq, hXe, hYe]
          ring
        have hzrec : c * r = z := by
          dsimp [Z] at hrZ
          field_simp [hc.ne'] at hrZ ⊢
          linarith
        refine
          ⟨((0 : ℝ), (Real.pi / 2, r)), ?_, ?_⟩
        · change 0 ≤ (0 : ℝ) ∧ 0 ≤ Real.pi / 2 ∧
            0 ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ Real.pi / 2 ∧
            0 ≤ r ∧ r ≤ 1
          exact ⟨le_rfl, by positivity, by positivity, le_rfl, hr0, hr1⟩
        · simp [ellipsoidMap, hxe, hye, hzrec]
      · have hrhopos : 0 < rho :=
          lt_of_le_of_ne hrho0 (Ne.symm hrhoe)
        have hZr : Z ≤ r := by
          apply (sq_le_sq₀ hZ hr0).mp
          rw [hrsq]
          calc
            Z ^ 2 ≤ Z ^ 2 + (X ^ 2 + Y ^ 2) :=
              le_add_of_nonneg_right
                (add_nonneg (sq_nonneg X) (sq_nonneg Y))
            _ = X ^ 2 + Y ^ 2 + Z ^ 2 := by ring
        have hYrho : Y ≤ rho := by
          apply (sq_le_sq₀ hY hrho0).mp
          rw [hrhosq]
          calc
            Y ^ 2 ≤ Y ^ 2 + X ^ 2 :=
              le_add_of_nonneg_right (sq_nonneg X)
            _ = X ^ 2 + Y ^ 2 := by ring
        have hXrho : X ≤ rho := by
          apply (sq_le_sq₀ hX hrho0).mp
          rw [hrhosq]
          exact le_add_of_nonneg_right (sq_nonneg Y)
        let psi : ℝ := Real.arcsin (Z / r)
        let phi : ℝ := Real.arcsin (Y / rho)
        have hZratio0 : 0 ≤ Z / r := div_nonneg hZ hr0
        have hZratio1 : Z / r ≤ 1 :=
          (div_le_one hrpos).mpr hZr
        have hYratio0 : 0 ≤ Y / rho := div_nonneg hY hrho0
        have hYratio1 : Y / rho ≤ 1 :=
          (div_le_one hrhopos).mpr hYrho
        have hpsi0 : 0 ≤ psi := by
          dsimp [psi]
          exact Real.arcsin_nonneg.mpr hZratio0
        have hpsi1 : psi ≤ Real.pi / 2 := by
          dsimp [psi]
          exact Real.arcsin_le_pi_div_two _
        have hphi0 : 0 ≤ phi := by
          dsimp [phi]
          exact Real.arcsin_nonneg.mpr hYratio0
        have hphi1 : phi ≤ Real.pi / 2 := by
          dsimp [phi]
          exact Real.arcsin_le_pi_div_two _
        have hsinpsi : Real.sin psi = Z / r := by
          dsimp [psi]
          exact Real.sin_arcsin (by linarith) hZratio1
        have hsinphi : Real.sin phi = Y / rho := by
          dsimp [phi]
          exact Real.sin_arcsin (by linarith) hYratio1
        have hcospsi : Real.cos psi = rho / r := by
          dsimp [psi]
          rw [Real.cos_arcsin]
          have hinside :
              1 - (Z / r) ^ 2 = (rho / r) ^ 2 := by
            field_simp [hre]
            rw [hrsq, hrhosq]
            ring
          rw [hinside, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (div_nonneg hrho0 hr0)]
        have hcosphi : Real.cos phi = X / rho := by
          dsimp [phi]
          rw [Real.cos_arcsin]
          have hinside :
              1 - (Y / rho) ^ 2 = (X / rho) ^ 2 := by
            field_simp [hrhoe]
            rw [hrhosq]
            ring
          rw [hinside, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (div_nonneg hX hrho0)]
        refine ⟨(phi, (psi, r)), ?_, ?_⟩
        · change 0 ≤ phi ∧ phi ≤ Real.pi / 2 ∧
            0 ≤ psi ∧ psi ≤ Real.pi / 2 ∧
            0 ≤ r ∧ r ≤ 1
          exact ⟨hphi0, hphi1, hpsi0, hpsi1, hr0, hr1⟩
        · simp only [ellipsoidMap]
          rw [hcosphi, hcospsi, hsinphi, hsinpsi]
          apply Prod.ext
          · dsimp [X]
            field_simp [ha.ne', hre, hrhoe]
          · apply Prod.ext
            · dsimp [Y]
              field_simp [hb.ne', hre, hrhoe]
            · dsimp [Z]
              field_simp [hc.ne', hre]

theorem gap3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    weightedIntegral a b c =
      8 *
        ∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              a * b * c * r ^ 2 * Real.cos psi *
                Real.sqrt (1 - r ^ 2) := by
  rw [weighted_radial_formula a b c ha hb hc]
  exact (coordinate_integral_formula a b c).symm

theorem gap4 (a b c : ℝ) :
    8 *
        (∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              a * b * c * r ^ 2 * Real.cos psi *
                Real.sqrt (1 - r ^ 2)) =
      4 * Real.pi *
        ∫ r in (0 : ℝ)..1,
          a * b * c * r ^ 2 * Real.sqrt (1 - r ^ 2) := by
  exact coordinate_integral_formula a b c

theorem gap5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    weightedIntegral a b c =
      4 * Real.pi *
        ∫ r in (0 : ℝ)..1,
          a * b * c * r ^ 2 * Real.sqrt (1 - r ^ 2) := by
  exact weighted_radial_formula a b c ha hb hc

theorem gap6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    weightedIntegral a b c =
      4 * Real.pi * a * b * c *
        ∫ t in (0 : ℝ)..Real.pi / 2,
          Real.sin t ^ 2 * Real.cos t ^ 2 := by
  rw [weighted_radial_formula a b c ha hb hc]
  rw [show (fun r : ℝ =>
      a * b * c * r ^ 2 * Real.sqrt (1 - r ^ 2)) =
    fun r => (a * b * c) *
      (r ^ 2 * Real.sqrt (1 - r ^ 2)) by
    funext r
    ring]
  rw [intervalIntegral.integral_const_mul, radial_trig_integral]
  ring

theorem gap7 (a b c : ℝ) :
    4 * Real.pi * a * b * c *
        (∫ t in (0 : ℝ)..Real.pi / 2,
          Real.sin t ^ 2 * Real.cos t ^ 2) =
      Real.pi * a * b * c / 2 *
        ∫ t in (0 : ℝ)..Real.pi / 2,
          (1 - Real.cos (4 * t)) := by
  have hpoint (t : ℝ) :
      Real.sin t ^ 2 * Real.cos t ^ 2 =
        (1 / 8 : ℝ) * (1 - Real.cos (4 * t)) := by
    have hcos := Real.cos_two_mul (2 * t)
    rw [show 2 * (2 * t) = 4 * t by ring] at hcos
    have hsin := Real.sin_two_mul t
    have hdiff :
        1 - Real.cos (4 * t) = 2 * Real.sin (2 * t) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (2 * t)]
    rw [hdiff, hsin]
    ring
  have hint :
      (∫ t in (0 : ℝ)..Real.pi / 2,
        Real.sin t ^ 2 * Real.cos t ^ 2) =
        (1 / 8 : ℝ) *
          ∫ t in (0 : ℝ)..Real.pi / 2,
            (1 - Real.cos (4 * t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    exact hpoint t
  rw [hint]
  ring

theorem gap8 (a b c : ℝ) :
    Real.pi * a * b * c / 2 *
        (∫ t in (0 : ℝ)..Real.pi / 2,
          (1 - Real.cos (4 * t))) =
      Real.pi ^ 2 * a * b * c / 4 := by
  have hcos :
      (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos (4 * t)) = 0 := by
    let F : ℝ → ℝ := fun t => Real.sin (4 * t) / 4
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
        HasDerivAt F (Real.cos (4 * t)) t := by
      intro t _
      dsimp [F]
      convert
        ((Real.hasDerivAt_sin (4 * t)).comp t
          ((hasDerivAt_id t).const_mul 4)).div_const 4 using 1 <;>
        ring
    have hi : IntervalIntegrable
        (fun t : ℝ => Real.cos (4 * t))
        MeasureTheory.volume 0 (Real.pi / 2) :=
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    dsimp [F]
    rw [show 4 * (Real.pi / 2) = 2 * Real.pi by ring,
      Real.sin_two_pi]
    norm_num
  have hi1 : IntervalIntegrable (fun _t : ℝ => (1 : ℝ))
      MeasureTheory.volume 0 (Real.pi / 2) :=
    continuous_const.intervalIntegrable _ _
  have hi4 : IntervalIntegrable (fun t : ℝ => Real.cos (4 * t))
      MeasureTheory.volume 0 (Real.pi / 2) :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hsub :
      (∫ t in (0 : ℝ)..Real.pi / 2,
        (1 - Real.cos (4 * t))) =
        (∫ _t in (0 : ℝ)..Real.pi / 2, (1 : ℝ)) -
          ∫ t in (0 : ℝ)..Real.pi / 2, Real.cos (4 * t) :=
    intervalIntegral.integral_sub hi1 hi4
  rw [hsub, intervalIntegral.integral_const, hcos]
  simp only [smul_eq_mul]
  ring

theorem gap9 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    weightedIntegral a b c =
      Real.pi ^ 2 * a * b * c / 4 := by
  calc
    weightedIntegral a b c =
        4 * Real.pi * a * b * c *
          ∫ t in (0 : ℝ)..Real.pi / 2,
            Real.sin t ^ 2 * Real.cos t ^ 2 :=
      gap6 a b c ha hb hc
    _ = Real.pi * a * b * c / 2 *
          ∫ t in (0 : ℝ)..Real.pi / 2,
            (1 - Real.cos (4 * t)) :=
      gap7 a b c
    _ = Real.pi ^ 2 * a * b * c / 4 :=
      gap8 a b c

end

end ProofGap.Exercise4090
