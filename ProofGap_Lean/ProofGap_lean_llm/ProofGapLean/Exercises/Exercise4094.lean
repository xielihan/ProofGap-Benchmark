import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4094

noncomputable section

open MeasureTheory
open scoped Interval

def region : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤
    p.1 + p.2.1 + p.2.2}

def integrand (p : ℝ × ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

def volume : ℝ :=
  ∫ _ in region, (1 : ℝ)

def integrandIntegral : ℝ :=
  ∫ p in region, integrand p

def average : ℝ :=
  integrandIntegral / volume

private def unitBall : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1}

private def unitDisk : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ 1}

private def halfDisk : Set (ℝ × ℝ) :=
  {q | 0 < q.1 ∧ q.1 ^ 2 + q.2 ^ 2 ≤ 1}
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


private def rho : ℝ := Real.sqrt 3 / 2

private theorem rho_pos : 0 < rho := by
  dsimp [rho]
  positivity

private theorem rho_sq : rho ^ 2 = 3 / 4 := by
  dsimp [rho]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

private def scale1 (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

private def scale3 (a b c : ℝ) :
    (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ)) :=
  (scale1 a).prodMap ((scale1 b).prodMap (scale1 c))

@[simp] private theorem scale3_apply (a b c : ℝ)
    (p : ℝ × (ℝ × ℝ)) :
    scale3 a b c p = (a * p.1, (b * p.2.1, c * p.2.2)) := by
  rcases p with ⟨x, y, z⟩
  simp [scale3, scale1]

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

private def center : ℝ × ℝ × ℝ :=
  ((1 / 2 : ℝ), ((1 / 2 : ℝ), (1 / 2 : ℝ)))

private def affineBallMap (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  center + scale3 rho rho rho p

@[simp] private theorem affineBallMap_apply (p : ℝ × ℝ × ℝ) :
    affineBallMap p =
      (1 / 2 + rho * p.1,
        (1 / 2 + rho * p.2.1, 1 / 2 + rho * p.2.2)) := by
  rcases p with ⟨x, y, z⟩
  simp [affineBallMap, center]

private theorem affine_image_unitBall :
    affineBallMap '' unitBall = region := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1 at hp
    simp only [region, Set.mem_setOf_eq, affineBallMap_apply]
    have hr := rho_sq
    nlinarith
  · intro hq
    change q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 ≤
      q.1 + q.2.1 + q.2.2 at hq
    let p : ℝ × ℝ × ℝ :=
      ((q.1 - 1 / 2) / rho,
        ((q.2.1 - 1 / 2) / rho, (q.2.2 - 1 / 2) / rho))
    have hmap : affineBallMap p = q := by
      rw [affineBallMap_apply]
      apply Prod.ext
      · dsimp [p]
        field_simp [rho_pos.ne']
        ring
      · apply Prod.ext
        · dsimp [p]
          field_simp [rho_pos.ne']
          ring
        · dsimp [p]
          field_simp [rho_pos.ne']
          ring
    refine ⟨p, ?_, hmap⟩
    change p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1
    have hcenter :
        (q.1 - 1 / 2) ^ 2 + (q.2.1 - 1 / 2) ^ 2 +
            (q.2.2 - 1 / 2) ^ 2 ≤ 3 / 4 := by
      nlinarith
    dsimp [p]
    simp only [div_pow, rho_sq]
    norm_num
    nlinarith

private theorem affine_injOn :
    Set.InjOn affineBallMap unitBall := by
  intro p hp q hq heq
  have h1 : rho * p.1 = rho * q.1 := by
    have h := congrArg Prod.fst heq
    simp only [affineBallMap_apply] at h
    linarith
  have h21 : rho * p.2.1 = rho * q.2.1 := by
    have h := congrArg (fun t => t.2.1) heq
    simp only [affineBallMap_apply] at h
    linarith
  have h22 : rho * p.2.2 = rho * q.2.2 := by
    have h := congrArg (fun t => t.2.2) heq
    simp only [affineBallMap_apply] at h
    linarith
  apply Prod.ext
  · exact mul_left_cancel₀ rho_pos.ne' h1
  · apply Prod.ext
    · exact mul_left_cancel₀ rho_pos.ne' h21
    · exact mul_left_cancel₀ rho_pos.ne' h22

private theorem affine_set_integral (g : ℝ × ℝ × ℝ → ℝ) :
    (∫ p in region, g p) =
      ∫ p in unitBall, rho ^ 3 * g (affineBallMap p) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ))) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hderiv (p : ℝ × ℝ × ℝ) :
      HasFDerivAt affineBallMap (scale3 rho rho rho) p := by
    have h :=
      (hasFDerivAt_const center p).add
        (scale3 rho rho rho).hasFDerivAt
    simpa [affineBallMap] using h
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) unitBall_closed.measurableSet
      (f := affineBallMap) (f' := fun _ => scale3 rho rho rho)
      (fun p hp => (hderiv p).hasFDerivWithinAt)
      affine_injOn g
  rw [affine_image_unitBall] at hchange
  have hdet :
      |(scale3 rho rho rho).det| = rho ^ 3 := by
    rw [det_scale3, abs_of_pos (mul_pos (mul_pos rho_pos rho_pos) rho_pos)]
    ring
  simpa only [hdet, smul_eq_mul] using hchange

private theorem unitBall_volume :
    (∫ _p in unitBall, (1 : ℝ)) = 4 / 3 * Real.pi := by
  have h :=
    radial_unitBall_formula (fun _ : ℝ => (1 : ℝ)) continuous_const
  rw [h]
  rw [show (fun r : ℝ => r ^ 2 * (1 : ℝ)) = fun r => r ^ 2 by
    funext r
    ring]
  rw [integral_pow]
  norm_num
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

private theorem neg_image_unitBall :
    scale3 (-1) (-1) (-1) '' unitBall = unitBall := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [unitBall] using hp
  · intro hq
    refine ⟨scale3 (-1) (-1) (-1) q, ?_, ?_⟩
    · simpa [unitBall] using hq
    · rcases q with ⟨x, y, z⟩
      simp

private theorem neg_injOn :
    Set.InjOn (scale3 (-1) (-1) (-1)) unitBall := by
  intro p hp q hq heq
  simp only [scale3_apply, neg_mul, one_mul, Prod.mk.injEq,
    neg_inj] at heq
  exact Prod.ext heq.1 (Prod.ext heq.2.1 heq.2.2)

private theorem unitBall_coordSum_integral :
    (∫ p in unitBall, p.1 + p.2.1 + p.2.2) = 0 := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ))) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let S : ℝ × ℝ × ℝ → ℝ := fun p => p.1 + p.2.1 + p.2.2
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) unitBall_closed.measurableSet
      (f := scale3 (-1) (-1) (-1))
      (f' := fun _ => scale3 (-1) (-1) (-1))
      (fun p hp =>
        (scale3 (-1) (-1) (-1)).hasFDerivAt.hasFDerivWithinAt)
      neg_injOn S
  rw [neg_image_unitBall] at hchange
  have hdet : |(scale3 (-1) (-1) (-1)).det| = 1 := by
    rw [det_scale3]
    norm_num
  have hneg :
      (∫ p in unitBall, S (scale3 (-1) (-1) (-1) p)) =
        -(∫ p in unitBall, S p) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with p
    simp [S]
    ring
  simp only [hdet, one_smul] at hchange
  rw [hneg] at hchange
  have : (∫ p in unitBall, S p) = 0 := by linarith
  simpa [S] using this

private theorem volume_value :
    volume = Real.sqrt 3 / 2 * Real.pi := by
  unfold volume
  rw [affine_set_integral (fun _ => (1 : ℝ))]
  simp only [mul_one]
  have hconst :
      (∫ _p in unitBall, rho ^ 3) =
        rho ^ 3 * ∫ _p in unitBall, (1 : ℝ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  rw [hconst, unitBall_volume]
  rw [show rho ^ 3 = 3 * Real.sqrt 3 / 8 by
    rw [show rho ^ 3 = rho ^ 2 * rho by ring, rho_sq]
    simp [rho]
    ring]
  ring

private theorem integrandIntegral_value :
    integrandIntegral = 3 * Real.sqrt 3 * Real.pi / 5 := by
  unfold integrandIntegral
  rw [affine_set_integral integrand]
  have hpoint (p : ℝ × ℝ × ℝ) :
      rho ^ 3 * integrand (affineBallMap p) =
        rho ^ 3 *
          (3 / 4 +
            rho * (p.1 + p.2.1 + p.2.2) +
            rho ^ 2 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) := by
    simp only [integrand, affineBallMap_apply]
    ring
  simp_rw [hpoint]
  rw [show (fun p : ℝ × ℝ × ℝ =>
      rho ^ 3 *
        (3 / 4 + rho * (p.1 + p.2.1 + p.2.2) +
          rho ^ 2 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))) =
      fun p =>
        rho ^ 3 * (3 / 4) +
          (rho ^ 4) * (p.1 + p.2.1 + p.2.2) +
          (rho ^ 5) * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) by
    funext p
    ring]
  have hconst :
      (∫ _p in unitBall, (3 / 4 : ℝ)) =
        (3 / 4 : ℝ) * ∫ _p in unitBall, (1 : ℝ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  have hsum : Continuous
      (fun p : ℝ × ℝ × ℝ => p.1 + p.2.1 + p.2.2) :=
    (continuous_fst.add (continuous_fst.comp continuous_snd)).add
      (continuous_snd.comp continuous_snd)
  have hsquares : Continuous
      (fun p : ℝ × ℝ × ℝ =>
        p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) :=
    ((continuous_fst.pow 2).add
      ((continuous_fst.comp continuous_snd).pow 2)).add
      ((continuous_snd.comp continuous_snd).pow 2)
  have hi0 : IntegrableOn
      (fun _p : ℝ × ℝ × ℝ => rho ^ 3 * (3 / 4)) unitBall :=
    continuous_const.continuousOn.integrableOn_compact unitBall_compact
  have hi1 : IntegrableOn
      (fun p : ℝ × ℝ × ℝ =>
        rho ^ 4 * (p.1 + p.2.1 + p.2.2)) unitBall :=
    (continuous_const.mul hsum).continuousOn.integrableOn_compact
      unitBall_compact
  have hi2 : IntegrableOn
      (fun p : ℝ × ℝ × ℝ =>
        rho ^ 5 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) unitBall :=
    (continuous_const.mul hsquares).continuousOn.integrableOn_compact
      unitBall_compact
  have hsplit :
      (∫ p in unitBall,
          rho ^ 3 * (3 / 4) +
            rho ^ 4 * (p.1 + p.2.1 + p.2.2) +
            rho ^ 5 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) =
        (∫ p in unitBall, rho ^ 3 * (3 / 4)) +
          (∫ p in unitBall,
            rho ^ 4 * (p.1 + p.2.1 + p.2.2)) +
          ∫ p in unitBall,
            rho ^ 5 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
    calc
      _ = (∫ p in unitBall,
              rho ^ 3 * (3 / 4) +
                rho ^ 4 * (p.1 + p.2.1 + p.2.2)) +
            ∫ p in unitBall,
              rho ^ 5 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
        exact integral_add (hi0.add hi1) hi2
      _ = _ := by
        rw [integral_add hi0 hi1]
  rw [hsplit, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    hconst, unitBall_volume, unitBall_coordSum_integral,
    unitBall_radiusSq_integral]
  have hr3 : rho ^ 3 = 3 * Real.sqrt 3 / 8 := by
    rw [show rho ^ 3 = rho ^ 2 * rho by ring, rho_sq]
    simp [rho]
    ring
  have hr4 : rho ^ 4 = 9 / 16 := by
    rw [show rho ^ 4 = (rho ^ 2) ^ 2 by ring, rho_sq]
    norm_num
  have hr5 : rho ^ 5 = 9 * Real.sqrt 3 / 32 := by
    rw [show rho ^ 5 = (rho ^ 2) ^ 2 * rho by ring, rho_sq]
    simp [rho]
    ring
  rw [hr3, hr4, hr5]
  ring

private theorem average_value :
    average = 6 / 5 := by
  unfold average
  rw [integrandIntegral_value, volume_value]
  field_simp [Real.pi_ne_zero,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
  ring

private theorem rho_cube : rho ^ 3 = 3 * Real.sqrt 3 / 8 := by
  rw [show rho ^ 3 = rho ^ 2 * rho by ring, rho_sq]
  simp [rho]
  ring

private theorem rho_fourth : rho ^ 4 = 9 / 16 := by
  rw [show rho ^ 4 = (rho ^ 2) ^ 2 by ring, rho_sq]
  norm_num

private theorem rho_fifth : rho ^ 5 = 9 * Real.sqrt 3 / 32 := by
  rw [show rho ^ 5 = (rho ^ 2) ^ 2 * rho by ring, rho_sq]
  simp [rho]
  ring

private theorem psi_cos_integral :
    (∫ psi in -Real.pi / 2..Real.pi / 2, Real.cos psi) = 2 := by
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring]
  rw [integral_cos, Real.sin_pi_div_two, Real.sin_neg,
    Real.sin_pi_div_two]
  norm_num

private theorem psi_sin_cos_integral :
    (∫ psi in -Real.pi / 2..Real.pi / 2,
      Real.sin psi * Real.cos psi) = 0 := by
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring]
  rw [integral_sin_mul_cos₁, Real.sin_pi_div_two, Real.sin_neg,
    Real.sin_pi_div_two]
  norm_num

private theorem psi_cos_sq_integral :
    (∫ psi in -Real.pi / 2..Real.pi / 2,
      Real.cos psi ^ 2) = Real.pi / 2 := by
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring]
  rw [integral_cos_sq]
  rw [Real.cos_pi_div_two, Real.cos_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
  ring

private theorem phi_cos_integral :
    (∫ phi in (0 : ℝ)..2 * Real.pi, Real.cos phi) = 0 := by
  rw [integral_cos, Real.sin_two_pi, Real.sin_zero]
  norm_num

private theorem phi_sin_integral :
    (∫ phi in (0 : ℝ)..2 * Real.pi, Real.sin phi) = 0 := by
  rw [integral_sin, Real.cos_zero, Real.cos_two_pi]
  norm_num

private theorem radial_full_integral (phi psi : ℝ) :
    (∫ r in (0 : ℝ)..rho,
      r ^ 2 * Real.cos psi *
        (3 / 4 + r ^ 2 + r * Real.sin psi +
          r * Real.cos phi * Real.cos psi +
          r * Real.sin phi * Real.cos psi)) =
      3 * Real.sqrt 3 / 20 * Real.cos psi +
        9 / 64 * (Real.sin psi * Real.cos psi) +
        9 / 64 * (Real.cos phi + Real.sin phi) *
          Real.cos psi ^ 2 := by
  have h2 : IntervalIntegrable (fun r : ℝ => r ^ 2)
      MeasureTheory.volume 0 rho :=
    (continuous_id.pow 2).intervalIntegrable 0 rho
  have h3 : IntervalIntegrable (fun r : ℝ => r ^ 3)
      MeasureTheory.volume 0 rho :=
    (continuous_id.pow 3).intervalIntegrable 0 rho
  have h4 : IntervalIntegrable (fun r : ℝ => r ^ 4)
      MeasureTheory.volume 0 rho :=
    (continuous_id.pow 4).intervalIntegrable 0 rho
  rw [show (fun r : ℝ =>
      r ^ 2 * Real.cos psi *
        (3 / 4 + r ^ 2 + r * Real.sin psi +
          r * Real.cos phi * Real.cos psi +
          r * Real.sin phi * Real.cos psi)) =
      fun r =>
        (3 / 4 * Real.cos psi) * r ^ 2 +
          Real.cos psi * r ^ 4 +
          (Real.cos psi *
            (Real.sin psi +
              (Real.cos phi + Real.sin phi) * Real.cos psi)) *
            r ^ 3 by
    funext r
    ring]
  rw [intervalIntegral.integral_add
      ((h2.const_mul (3 / 4 * Real.cos psi)).add
        (h4.const_mul (Real.cos psi)))
      (h3.const_mul
        (Real.cos psi *
          (Real.sin psi +
            (Real.cos phi + Real.sin phi) * Real.cos psi))),
    intervalIntegral.integral_add
      (h2.const_mul (3 / 4 * Real.cos psi))
      (h4.const_mul (Real.cos psi)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow]
  norm_num
  rw [rho_cube, rho_fourth, rho_fifth]
  ring

private theorem radial_even_integral (psi : ℝ) :
    (∫ r in (0 : ℝ)..rho,
      r ^ 2 * Real.cos psi * (3 / 4 + r ^ 2)) =
      3 * Real.sqrt 3 / 20 * Real.cos psi := by
  have h2 : IntervalIntegrable (fun r : ℝ => r ^ 2)
      MeasureTheory.volume 0 rho :=
    (continuous_id.pow 2).intervalIntegrable 0 rho
  have h4 : IntervalIntegrable (fun r : ℝ => r ^ 4)
      MeasureTheory.volume 0 rho :=
    (continuous_id.pow 4).intervalIntegrable 0 rho
  rw [show (fun r : ℝ =>
      r ^ 2 * Real.cos psi * (3 / 4 + r ^ 2)) =
      fun r =>
        (3 / 4 * Real.cos psi) * r ^ 2 +
          Real.cos psi * r ^ 4 by
    funext r
    ring]
  rw [intervalIntegral.integral_add
      (h2.const_mul (3 / 4 * Real.cos psi))
      (h4.const_mul (Real.cos psi)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num
  rw [rho_cube, rho_fifth]
  ring

private theorem psi_full_integral (phi : ℝ) :
    (∫ psi in -Real.pi / 2..Real.pi / 2,
      (3 * Real.sqrt 3 / 20 * Real.cos psi +
        9 / 64 * (Real.sin psi * Real.cos psi) +
        9 / 64 * (Real.cos phi + Real.sin phi) *
          Real.cos psi ^ 2)) =
      3 * Real.sqrt 3 / 10 +
        9 * Real.pi / 128 * (Real.cos phi + Real.sin phi) := by
  have hcos : IntervalIntegrable (fun psi : ℝ => Real.cos psi)
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) :=
    Real.continuous_cos.intervalIntegrable _ _
  have hsincos : IntervalIntegrable
      (fun psi : ℝ => Real.sin psi * Real.cos psi)
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) :=
    (Real.continuous_sin.mul Real.continuous_cos).intervalIntegrable _ _
  have hcos2 : IntervalIntegrable
      (fun psi : ℝ => Real.cos psi ^ 2)
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) :=
    (Real.continuous_cos.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add
      ((hcos.const_mul (3 * Real.sqrt 3 / 20)).add
        (hsincos.const_mul (9 / 64)))
      (hcos2.const_mul
        (9 / 64 * (Real.cos phi + Real.sin phi))),
    intervalIntegral.integral_add
      (hcos.const_mul (3 * Real.sqrt 3 / 20))
      (hsincos.const_mul (9 / 64)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    psi_cos_integral, psi_sin_cos_integral, psi_cos_sq_integral]
  ring

private theorem nested_full_value :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
      ∫ psi in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..rho,
          r ^ 2 * Real.cos psi *
            (3 / 4 + r ^ 2 + r * Real.sin psi +
              r * Real.cos phi * Real.cos psi +
              r * Real.sin phi * Real.cos psi)) =
      3 * Real.sqrt 3 * Real.pi / 5 := by
  simp_rw [radial_full_integral, psi_full_integral]
  have hcos : IntervalIntegrable (fun phi : ℝ => Real.cos phi)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    Real.continuous_cos.intervalIntegrable _ _
  have hsin : IntervalIntegrable (fun phi : ℝ => Real.sin phi)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    Real.continuous_sin.intervalIntegrable _ _
  have hconst : IntervalIntegrable
      (fun _phi : ℝ => 3 * Real.sqrt 3 / 10)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  rw [show (fun phi : ℝ =>
      3 * Real.sqrt 3 / 10 +
        9 * Real.pi / 128 * (Real.cos phi + Real.sin phi)) =
      fun phi =>
        3 * Real.sqrt 3 / 10 +
          (9 * Real.pi / 128) * Real.cos phi +
          (9 * Real.pi / 128) * Real.sin phi by
    funext phi
    ring]
  rw [intervalIntegral.integral_add
      (hconst.add (hcos.const_mul (9 * Real.pi / 128)))
      (hsin.const_mul (9 * Real.pi / 128)),
    intervalIntegral.integral_add hconst
      (hcos.const_mul (9 * Real.pi / 128)),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    phi_cos_integral, phi_sin_integral]
  simp only [smul_eq_mul]
  ring

private theorem reduced_nested_value :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
      ∫ psi in -Real.pi / 2..Real.pi / 2,
        3 * Real.sqrt 3 / 20 * Real.cos psi) =
      3 * Real.sqrt 3 * Real.pi / 5 := by
  rw [show (fun psi : ℝ =>
      3 * Real.sqrt 3 / 20 * Real.cos psi) =
      fun psi => (3 * Real.sqrt 3 / 20) * Real.cos psi by rfl]
  rw [intervalIntegral.integral_const_mul, psi_cos_integral]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private theorem even_nested_value :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
      ∫ psi in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..rho,
          r ^ 2 * Real.cos psi * (3 / 4 + r ^ 2)) =
      3 * Real.sqrt 3 * Real.pi / 5 := by
  simp_rw [radial_even_integral]
  exact reduced_nested_value

theorem gap1 (x y z : ℝ) :
    x ^ 2 + y ^ 2 + z ^ 2 ≤ x + y + z ↔
      (x - 1 / 2) ^ 2 + (y - 1 / 2) ^ 2 +
        (z - 1 / 2) ^ 2 ≤ 3 / 4 := by
  constructor <;> intro h <;> nlinarith

theorem gap2 :
    volume = 4 / 3 * Real.pi * (Real.sqrt 3 / 2) ^ 3 := by
  change volume = 4 / 3 * Real.pi * rho ^ 3
  rw [volume_value, rho_cube]
  ring

theorem gap3 :
    4 / 3 * Real.pi * (Real.sqrt 3 / 2) ^ 3 =
      Real.sqrt 3 / 2 * Real.pi := by
  change 4 / 3 * Real.pi * rho ^ 3 =
    Real.sqrt 3 / 2 * Real.pi
  rw [rho_cube]
  ring

theorem gap4 :
    volume = Real.sqrt 3 / 2 * Real.pi := by
  exact volume_value

theorem gap5 :
    average =
      1 / volume *
        ∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..Real.sqrt 3 / 2,
              r ^ 2 * Real.cos psi *
                (3 / 4 + r ^ 2 + r * Real.sin psi +
                  r * Real.cos phi * Real.cos psi +
                  r * Real.sin phi * Real.cos psi) := by
  rw [average_value, volume_value]
  change
    (6 / 5 : ℝ) =
      1 / (Real.sqrt 3 / 2 * Real.pi) *
        (∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..rho,
              r ^ 2 * Real.cos psi *
                (3 / 4 + r ^ 2 + r * Real.sin psi +
                  r * Real.cos phi * Real.cos psi +
                  r * Real.sin phi * Real.cos psi))
  rw [nested_full_value]
  field_simp [Real.pi_ne_zero,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem gap6 :
    average =
      1 / volume *
        ∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..Real.sqrt 3 / 2,
              r ^ 2 * Real.cos psi * (3 / 4 + r ^ 2) := by
  rw [average_value, volume_value]
  change
    (6 / 5 : ℝ) =
      1 / (Real.sqrt 3 / 2 * Real.pi) *
        (∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..rho,
              r ^ 2 * Real.cos psi * (3 / 4 + r ^ 2))
  rw [even_nested_value]
  field_simp [Real.pi_ne_zero,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem gap7 :
    average =
      1 / volume *
        ∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in -Real.pi / 2..Real.pi / 2,
            3 * Real.sqrt 3 / 20 * Real.cos psi := by
  rw [average_value, volume_value, reduced_nested_value]
  field_simp [Real.pi_ne_zero,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem gap8 :
    1 / volume *
        (∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in -Real.pi / 2..Real.pi / 2,
            3 * Real.sqrt 3 / 20 * Real.cos psi) =
      1 / volume *
        ∫ phi in (0 : ℝ)..2 * Real.pi,
          3 * Real.sqrt 3 / 10 := by
  rw [reduced_nested_value, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap9 :
    average =
      1 / volume *
        ∫ phi in (0 : ℝ)..2 * Real.pi,
          3 * Real.sqrt 3 / 10 := by
  rw [average_value, volume_value, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
  ring

theorem gap10 :
    average =
      1 / volume * (3 * Real.sqrt 3 * Real.pi / 5) := by
  rw [average_value, volume_value]
  field_simp [Real.pi_ne_zero,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem gap11 :
    1 / volume * (3 * Real.sqrt 3 * Real.pi / 5) =
      2 / (Real.sqrt 3 * Real.pi) *
        (3 * Real.sqrt 3 * Real.pi / 5) := by
  rw [volume_value]
  ring

theorem gap12 :
    2 / (Real.sqrt 3 * Real.pi) *
        (3 * Real.sqrt 3 * Real.pi / 5) =
      6 / 5 := by
  field_simp [Real.pi_ne_zero,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem gap13 :
    average = 6 / 5 := by
  exact average_value

end

end ProofGap.Exercise4094
