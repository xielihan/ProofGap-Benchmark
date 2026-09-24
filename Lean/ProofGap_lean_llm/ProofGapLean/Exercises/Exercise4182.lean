import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.MetricSpace.Bounded

namespace ProofGap.Exercise4182

noncomputable section

open MeasureTheory
open scoped Interval Real

def disk : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

def quadraticForm (z : ℝ × ℝ) : ℝ :=
  z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2

def modelWeight (p : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 / Real.rpow (quadraticForm z) p

def weightedIntegrand (phi : ℝ × ℝ → ℝ) (p : ℝ)
    (z : ℝ × ℝ) : ℝ :=
  phi z / Real.rpow (quadraticForm z) p

def modelIntegral (p : ℝ) : ℝ :=
  ∫ z in disk, modelWeight p z

def weightedIntegral (phi : ℝ × ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ z in disk, weightedIntegrand phi p z

def angleFactor (theta : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * Real.sin (2 * theta)

def angularIntegral (p : ℝ) : ℝ :=
  ∫ theta in (0 : ℝ)..2 * Real.pi,
    1 / Real.rpow (angleFactor theta) p

def radialWeight (p r : ℝ) : ℝ :=
  1 / Real.rpow r (2 * p - 1)

def radialIntegral (p : ℝ) : ℝ :=
  ∫ r in Set.Ioc (0 : ℝ) 1, radialWeight p r

theorem gap1 (x y : ℝ) :
    x ^ 2 + x * y + y ^ 2 =
      (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) +
        (1 / 2 : ℝ) * (x + y) ^ 2 := by
  ring

theorem gap2 (x y : ℝ) (hne : x ≠ 0 ∨ y ≠ 0) :
    0 <
      (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) +
        (1 / 2 : ℝ) * (x + y) ^ 2 := by
  rcases hne with hx | hy
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y, sq_nonneg (x + y)]
  · nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy, sq_nonneg (x + y)]

theorem gap3 (z : ℝ × ℝ) (hne : z ≠ (0, 0)) :
    0 < quadraticForm z := by
  have hcoord : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext <;> simp [h.1, h.2]
  rw [quadraticForm, gap1]
  exact gap2 z.1 z.2 hcoord

theorem gap4 (phi : ℝ × ℝ → ℝ) (m p : ℝ)
    (z : ℝ × ℝ) (hz : z ∈ disk) (hne : z ≠ (0, 0))
    (hm : ∀ w ∈ disk, m ≤ |phi w|) :
    m / Real.rpow (quadraticForm z) p ≤
      |phi z| / Real.rpow (quadraticForm z) p := by
  exact div_le_div_of_nonneg_right (hm z hz)
    (Real.rpow_pos_of_pos (gap3 z hne) p).le

theorem gap5 (phi : ℝ × ℝ → ℝ) (M p : ℝ)
    (z : ℝ × ℝ) (hz : z ∈ disk) (hne : z ≠ (0, 0))
    (hM : ∀ w ∈ disk, |phi w| ≤ M) :
    |phi z| / Real.rpow (quadraticForm z) p ≤
      M / Real.rpow (quadraticForm z) p := by
  exact div_le_div_of_nonneg_right (hM z hz)
    (Real.rpow_pos_of_pos (gap3 z hne) p).le

theorem gap6 (phi : ℝ × ℝ → ℝ) (m M p : ℝ)
    (z : ℝ × ℝ) (hz : z ∈ disk) (hne : z ≠ (0, 0))
    (hm : ∀ w ∈ disk, m ≤ |phi w|)
    (hM : ∀ w ∈ disk, |phi w| ≤ M) :
    m / Real.rpow (quadraticForm z) p ≤
      M / Real.rpow (quadraticForm z) p := by
  exact (gap4 phi m p z hz hne hm).trans
    (gap5 phi M p z hz hne hM)

private theorem radialWeight_eq_rpow
    (p r : ℝ) (hr : 0 < r) :
    radialWeight p r = Real.rpow r (1 - 2 * p) := by
  unfold radialWeight
  rw [show 2 * p - 1 = -(1 - 2 * p) by ring]
  have hneg :
      Real.rpow r (-(1 - 2 * p)) =
        (Real.rpow r (1 - 2 * p))⁻¹ :=
    Real.rpow_neg hr.le (1 - 2 * p)
  rw [hneg]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hr (1 - 2 * p))]

private theorem radialWeight_integrable_iff (p : ℝ) :
    IntegrableOn (radialWeight p) (Set.Ioc (0 : ℝ) 1) ↔ p < 1 := by
  have hsets :
      Set.Ioc (0 : ℝ) 1 =ᵐ[volume] Set.Ioo (0 : ℝ) 1 :=
    Ioo_ae_eq_Ioc.symm
  calc
    IntegrableOn (radialWeight p) (Set.Ioc (0 : ℝ) 1) ↔
        IntegrableOn (radialWeight p) (Set.Ioo (0 : ℝ) 1) :=
      integrableOn_congr_set_ae hsets
    _ ↔ IntegrableOn (fun r : ℝ => Real.rpow r (1 - 2 * p))
          (Set.Ioo (0 : ℝ) 1) := by
      apply integrableOn_congr_fun
      · intro r hr
        exact radialWeight_eq_rpow p r hr.1
      · exact measurableSet_Ioo
    _ ↔ -1 < 1 - 2 * p :=
      intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one
    _ ↔ p < 1 := by
      constructor <;> intro h <;> linarith

theorem gap11 (p : ℝ) :
    (IntegrableOn (radialWeight p) (Set.Ioc (0 : ℝ) 1) ↔ p < 1) ∧
      (p < 1 →
        radialIntegral p = 1 / (2 * (1 - p))) := by
  refine ⟨radialWeight_integrable_iff p, ?_⟩
  intro hp
  unfold radialIntegral
  calc
    (∫ r in Set.Ioc (0 : ℝ) 1, radialWeight p r) =
        ∫ r in Set.Ioc (0 : ℝ) 1, Real.rpow r (1 - 2 * p) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact radialWeight_eq_rpow p r hr.1
    _ = ∫ r in (0 : ℝ)..1, Real.rpow r (1 - 2 * p) := by
      rw [intervalIntegral.integral_of_le zero_le_one]
    _ = (Real.rpow 1 ((1 - 2 * p) + 1) -
          Real.rpow 0 ((1 - 2 * p) + 1)) /
          ((1 - 2 * p) + 1) :=
      integral_rpow (Or.inl (by linarith))
    _ = 1 / (2 * (1 - p)) := by
      have hexp : 0 < 2 * (1 - p) := by linarith
      have hone :
          Real.rpow 1 ((1 - 2 * p) + 1) = 1 := by
        change (1 : ℝ) ^ ((1 - 2 * p) + 1) = 1
        exact Real.one_rpow _
      have hzero :
          Real.rpow 0 ((1 - 2 * p) + 1) = 0 := by
        change (0 : ℝ) ^ ((1 - 2 * p) + 1) = 0
        exact Real.zero_rpow (by linarith)
      rw [hone, hzero]
      ring

private theorem disk_measurable : MeasurableSet disk := by
  unfold disk
  measurability

private theorem angleFactor_pos (theta : ℝ) :
    0 < angleFactor theta := by
  unfold angleFactor
  nlinarith [Real.neg_one_le_sin (2 * theta)]

private theorem measurable_rpow (s : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x s) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private def angleWeight (p theta : ℝ) : ℝ :=
  1 / Real.rpow (angleFactor theta) p

private theorem angleWeight_continuous (p : ℝ) :
    Continuous (angleWeight p) := by
  unfold angleWeight angleFactor
  apply Continuous.div continuous_const
  · apply Continuous.rpow_const
    · fun_prop
    · intro theta
      exact Or.inl (ne_of_gt (angleFactor_pos theta))
  · intro theta
    exact ne_of_gt (Real.rpow_pos_of_pos (angleFactor_pos theta) p)

private theorem radialWeight_measurable (p : ℝ) :
    Measurable (radialWeight p) := by
  unfold radialWeight
  exact measurable_const.div (measurable_rpow (2 * p - 1))

private theorem angleWeight_integrableOn (p : ℝ) :
    IntegrableOn (angleWeight p)
      (Set.Ioo (-Real.pi) Real.pi) := by
  exact
    ((angleWeight_continuous p).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self

private theorem exists_pos_le_angleWeight (p : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ theta : ℝ, c ≤ angleWeight p theta := by
  by_cases hp : 0 ≤ p
  · let c : ℝ := 1 / Real.rpow (3 / 2 : ℝ) p
    have hc : 0 < c := by
      unfold c
      exact one_div_pos.2
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2) p)
    refine ⟨c, hc, ?_⟩
    intro theta
    have haf : angleFactor theta ≤ (3 / 2 : ℝ) := by
      unfold angleFactor
      nlinarith [Real.sin_le_one (2 * theta)]
    have hr :=
      Real.rpow_le_rpow (angleFactor_pos theta).le haf hp
    unfold c angleWeight
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (angleFactor_pos theta) p) hr
  · have hp' : p ≤ 0 := le_of_not_ge hp
    let c : ℝ := 1 / Real.rpow (1 / 2 : ℝ) p
    have hc : 0 < c := by
      unfold c
      exact one_div_pos.2
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) p)
    refine ⟨c, hc, ?_⟩
    intro theta
    have haf : (1 / 2 : ℝ) ≤ angleFactor theta := by
      unfold angleFactor
      nlinarith [Real.neg_one_le_sin (2 * theta)]
    have hr :=
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) haf hp'
    unfold c angleWeight
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (angleFactor_pos theta) p) hr

private theorem angleWeight_periodic (p : ℝ) :
    Function.Periodic (angleWeight p) (2 * Real.pi) := by
  intro theta
  have hsin :
      Real.sin (2 * (theta + 2 * Real.pi)) =
        Real.sin (2 * theta) := by
    calc
      Real.sin (2 * (theta + 2 * Real.pi)) =
        Real.sin (2 * theta + (2 : ℕ) * (2 * Real.pi)) := by
        congr 1
        push_cast
        ring
      _ = Real.sin (2 * theta) :=
        Real.sin_add_nat_mul_two_pi (2 * theta) 2
  unfold angleWeight angleFactor
  rw [hsin]

private theorem quadraticForm_polar (r theta : ℝ) :
    quadraticForm (polarCoord.symm (r, theta)) =
      r ^ 2 * angleFactor theta := by
  simp only [polarCoord_symm_apply]
  unfold quadraticForm angleFactor
  rw [Real.sin_two_mul]
  nlinarith [Real.cos_sq_add_sin_sq theta]

private theorem polar_mem_disk_iff
    (r theta : ℝ) (hr : 0 < r) :
    polarCoord.symm (r, theta) ∈ disk ↔ r ≤ 1 := by
  simp only [polarCoord_symm_apply]
  unfold disk
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have hs := Real.sin_sq_add_cos_sq theta
    have hr0 : 0 ≤ r := hr.le
    nlinarith [sq_nonneg (r - 1)]
  · intro h
    have hs := Real.sin_sq_add_cos_sq theta
    nlinarith [mul_nonneg hr.le (sub_nonneg.2 h)]

private theorem polar_model_factor
    (p r theta : ℝ) (hr : 0 < r) :
    r * modelWeight p (polarCoord.symm (r, theta)) =
      radialWeight p r * angleWeight p theta := by
  have ha : 0 < angleFactor theta := angleFactor_pos theta
  have hq :
      Real.rpow
          (quadraticForm (polarCoord.symm (r, theta))) p =
        Real.rpow (r ^ 2) p * Real.rpow (angleFactor theta) p := by
    rw [quadraticForm_polar]
    exact Real.mul_rpow (sq_nonneg r) ha.le
  have hrsq :
      Real.rpow (r ^ 2) p = Real.rpow r (2 * p) := by
    calc
      Real.rpow (r ^ 2) p =
          Real.rpow (Real.rpow r (2 : ℝ)) p := by
        congr 2
        exact (Real.rpow_natCast r 2).symm
      _ = Real.rpow r (2 * p) :=
        (Real.rpow_mul hr.le 2 p).symm
  have hradd :
      Real.rpow r (2 * p) =
        Real.rpow r (2 * p - 1) * r := by
    calc
      Real.rpow r (2 * p) =
          Real.rpow r ((2 * p - 1) + 1) := by congr 2 <;> ring
      _ = Real.rpow r (2 * p - 1) * Real.rpow r 1 :=
        Real.rpow_add hr (2 * p - 1) 1
      _ = Real.rpow r (2 * p - 1) * r := by
        change Real.rpow r (2 * p - 1) * r ^ (1 : ℝ) =
          Real.rpow r (2 * p - 1) * r
        rw [Real.rpow_one]
  have hrpow : Real.rpow r (2 * p - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hr (2 * p - 1))
  have hapow : Real.rpow (angleFactor theta) p ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ha p)
  unfold modelWeight radialWeight angleWeight
  rw [hq, hrsq, hradd]
  field_simp [hr.ne', hrpow, hapow]

private theorem angular_setIntegral_eq (p : ℝ) :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi, angleWeight p theta) =
      angularIntegral p := by
  have hnegpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  calc
    (∫ theta in Set.Ioo (-Real.pi) Real.pi, angleWeight p theta) =
        ∫ theta in (-Real.pi)..Real.pi, angleWeight p theta := by
      rw [intervalIntegral.integral_of_le hnegpi]
      exact setIntegral_congr_set Ioo_ae_eq_Ioc
    _ = ∫ theta in (0 : ℝ)..2 * Real.pi, angleWeight p theta := by
      simpa [two_mul] using
        (angleWeight_periodic p).intervalIntegral_add_eq (-Real.pi) 0
    _ = angularIntegral p := by rfl

private theorem integrable_iff_polar
    (F : ℝ × ℝ → ℝ) :
    Integrable F volume ↔
      IntegrableOn
        (fun q : ℝ × ℝ => q.1 • F (polarCoord.symm q))
        polarCoord.target volume := by
  have hjac :=
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := (volume : Measure (ℝ × ℝ)))
      polarCoord.open_target.measurableSet
      (fun q _ => (hasFDerivAt_polarCoord_symm q).hasFDerivWithinAt)
      polarCoord.symm.injOn F
  rw [polarCoord.symm_image_target_eq_source] at hjac
  calc
    Integrable F volume ↔ IntegrableOn F Set.univ volume := by
      rw [IntegrableOn, Measure.restrict_univ]
    _ ↔ IntegrableOn F polarCoord.source volume :=
      integrableOn_congr_set_ae polarCoord_source_ae_eq_univ.symm
    _ ↔ IntegrableOn
        (fun q : ℝ × ℝ =>
          |(fderivPolarCoordSymm q).det| • F (polarCoord.symm q))
        polarCoord.target volume := hjac
    _ ↔ IntegrableOn
        (fun q : ℝ × ℝ => q.1 • F (polarCoord.symm q))
        polarCoord.target volume := by
      apply integrableOn_congr_fun
      · intro q hq
        change
          |(fderivPolarCoordSymm q).det| • F (polarCoord.symm q) =
            q.1 • F (polarCoord.symm q)
        rw [det_fderivPolarCoordSymm, abs_of_pos hq.1]
      · exact polarCoord.open_target.measurableSet

private theorem polar_model_indicator_eq
    (p : ℝ) (q : ℝ × ℝ) (hq : q ∈ polarCoord.target) :
    q.1 • disk.indicator (modelWeight p) (polarCoord.symm q) =
      (Set.Iic (1 : ℝ)).indicator (radialWeight p) q.1 *
        angleWeight p q.2 := by
  have hr : 0 < q.1 := hq.1
  change
    q.1 * disk.indicator (modelWeight p)
        (polarCoord.symm (q.1, q.2)) =
      (Set.Iic (1 : ℝ)).indicator (radialWeight p) q.1 *
        angleWeight p q.2
  by_cases hr1 : q.1 ≤ 1
  · have hdisk := (polar_mem_disk_iff q.1 q.2 hr).2 hr1
    have hrmem : q.1 ∈ Set.Iic (1 : ℝ) := hr1
    rw [Set.indicator_of_mem hdisk, Set.indicator_of_mem hrmem]
    exact polar_model_factor p q.1 q.2 hr
  · have hdisk :
        polarCoord.symm (q.1, q.2) ∉ disk := by
      intro hdisk
      exact hr1 ((polar_mem_disk_iff q.1 q.2 hr).1 hdisk)
    have hrmem : q.1 ∉ Set.Iic (1 : ℝ) := hr1
    rw [Set.indicator_of_notMem hdisk, Set.indicator_of_notMem hrmem]
    simp

private theorem polar_model_integrable_iff_product (p : ℝ) :
    IntegrableOn
        (fun q : ℝ × ℝ =>
          q.1 • disk.indicator (modelWeight p) (polarCoord.symm q))
        polarCoord.target volume ↔
      IntegrableOn
        (fun q : ℝ × ℝ =>
          radialWeight p q.1 * angleWeight p q.2)
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        volume := by
  let separated : ℝ × ℝ → ℝ := fun q =>
    radialWeight p q.1 * angleWeight p q.2
  let radialCut : ℝ × ℝ → ℝ := fun q =>
    (Set.Iic (1 : ℝ)).indicator (radialWeight p) q.1 *
      angleWeight p q.2
  calc
    IntegrableOn
        (fun q : ℝ × ℝ =>
          q.1 • disk.indicator (modelWeight p) (polarCoord.symm q))
        polarCoord.target volume ↔
        IntegrableOn radialCut polarCoord.target volume := by
      apply integrableOn_congr_fun
      · intro q hq
        exact polar_model_indicator_eq p q hq
      · exact polarCoord.open_target.measurableSet
    _ ↔ IntegrableOn separated
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        volume := by
      have hfun :
          radialCut =
            (Set.Iic (1 : ℝ) ×ˢ Set.univ).indicator separated := by
        funext q
        by_cases hq : q.1 ≤ 1
        · have hmem : q ∈ Set.Iic (1 : ℝ) ×ˢ Set.univ := ⟨hq, Set.mem_univ _⟩
          simp [radialCut, separated, hq, hmem]
        · have hmem : q ∉ Set.Iic (1 : ℝ) ×ˢ Set.univ := by
            simpa using hq
          simp [radialCut, separated, hq, hmem]
      unfold IntegrableOn
      rw [hfun, integrable_indicator_iff
        (measurableSet_Iic.prod MeasurableSet.univ)]
      change
        Integrable separated
            ((volume.restrict polarCoord.target).restrict
              (Set.Iic (1 : ℝ) ×ˢ Set.univ)) ↔
          Integrable separated
            (volume.restrict
              (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi))
      rw [Measure.restrict_restrict
        (measurableSet_Iic.prod MeasurableSet.univ)]
      have hset :
          (Set.Iic (1 : ℝ) ×ˢ Set.univ) ∩ polarCoord.target =
            Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        ext q
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Iic,
          Set.mem_univ, and_true, polarCoord_target, Set.mem_setOf_eq,
          Set.mem_Ioc, Set.mem_Ioo]
        aesop
      rw [hset]

private theorem separated_integrable_iff_radial (p : ℝ) :
    IntegrableOn
        (fun q : ℝ × ℝ =>
          radialWeight p q.1 * angleWeight p q.2)
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        volume ↔
      IntegrableOn (radialWeight p) (Set.Ioc (0 : ℝ) 1)
        volume := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioo (-Real.pi) Real.pi)
  have hν : ν ≠ 0 := by
    unfold ν
    intro hzero
    have hmeasure :
        volume (Set.Ioo (-Real.pi) Real.pi) = 0 :=
      Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Ioo] at hmeasure
    exact
      (ne_of_gt ((ENNReal.ofReal_pos).2 (by
        linarith [Real.pi_pos]))) hmeasure
  change
    Integrable
        (fun q : ℝ × ℝ =>
          radialWeight p q.1 * angleWeight p q.2)
        (volume.restrict
          (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)) ↔
      Integrable (radialWeight p)
        (volume.restrict (Set.Ioc (0 : ℝ) 1))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  change
    Integrable
        (fun q : ℝ × ℝ =>
          radialWeight p q.1 * angleWeight p q.2)
        (μ.prod ν) ↔
      Integrable (radialWeight p) μ
  constructor
  · intro hprod
    obtain ⟨c, hc, hcle⟩ := exists_pos_le_angleWeight p
    have hscaled :
        Integrable
          (fun q : ℝ × ℝ =>
            c⁻¹ *
              (radialWeight p q.1 * angleWeight p q.2))
          (μ.prod ν) :=
      hprod.const_mul c⁻¹
    have hqpos : ∀ᵐ q : ℝ × ℝ ∂μ.prod ν, 0 < q.1 := by
      have hrpos : ∀ᵐ r : ℝ ∂μ, 0 < r := by
        unfold μ
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hr.1
      change ∀ᵐ q : ℝ × ℝ ∂μ.prod ν, q.1 ∈ Set.Ioi (0 : ℝ)
      rw [Measure.ae_prod_iff_ae_ae
        (measurableSet_Ioi.preimage measurable_fst)]
      filter_upwards [hrpos] with r hr
      exact ae_of_all _ (fun _ => hr)
    have hlift :
        Integrable (fun q : ℝ × ℝ => radialWeight p q.1)
          (μ.prod ν) := by
      apply hscaled.mono'
      · exact
          (radialWeight_measurable p).comp measurable_fst
            |>.aestronglyMeasurable
      · filter_upwards [hqpos] with q hq
        have hcangle := hcle q.2
        have hangle : 0 < angleWeight p q.2 := by
          unfold angleWeight
          exact one_div_pos.2
            (Real.rpow_pos_of_pos (angleFactor_pos q.2) p)
        have hradial : 0 ≤ radialWeight p q.1 := by
          unfold radialWeight
          exact one_div_nonneg.2 (Real.rpow_nonneg hq.le _)
        rw [Real.norm_eq_abs, abs_of_nonneg hradial]
        have hmul :
            radialWeight p q.1 * c ≤
              radialWeight p q.1 * angleWeight p q.2 :=
          mul_le_mul_of_nonneg_left hcangle hradial
        rw [inv_mul_eq_div]
        exact (le_div_iff₀ hc).2 hmul
    exact hlift.of_comp_fst hν
  · intro hradial
    have hangle :
        Integrable (angleWeight p) ν := by
      exact angleWeight_integrableOn p
    exact hradial.mul_prod hangle

private theorem modelWeight_integrable_iff (p : ℝ) :
    IntegrableOn (modelWeight p) disk volume ↔ p < 1 := by
  calc
    IntegrableOn (modelWeight p) disk volume ↔
        Integrable (disk.indicator (modelWeight p)) volume :=
      (integrable_indicator_iff disk_measurable).symm
    _ ↔ IntegrableOn
        (fun q : ℝ × ℝ =>
          q.1 • disk.indicator (modelWeight p) (polarCoord.symm q))
        polarCoord.target volume :=
      integrable_iff_polar (disk.indicator (modelWeight p))
    _ ↔ IntegrableOn
        (fun q : ℝ × ℝ =>
          radialWeight p q.1 * angleWeight p q.2)
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        volume :=
      polar_model_integrable_iff_product p
    _ ↔ IntegrableOn (radialWeight p) (Set.Ioc (0 : ℝ) 1)
        volume :=
      separated_integrable_iff_radial p
    _ ↔ p < 1 := radialWeight_integrable_iff p

private theorem zero_mem_disk : ((0, 0) : ℝ × ℝ) ∈ disk := by
  simp [disk]

private theorem quadraticForm_nonneg (z : ℝ × ℝ) :
    0 ≤ quadraticForm z := by
  rw [quadraticForm, gap1]
  positivity

private theorem modelWeight_nonneg (p : ℝ) (z : ℝ × ℝ) :
    0 ≤ modelWeight p z := by
  unfold modelWeight
  exact one_div_nonneg.2
    (Real.rpow_nonneg (quadraticForm_nonneg z) p)

private theorem modelWeight_measurable (p : ℝ) :
    Measurable (modelWeight p) := by
  unfold modelWeight
  apply Measurable.div measurable_const
  apply (measurable_rpow p).comp
  unfold quadraticForm
  measurability

private theorem weightedIntegrand_eq_mul
    (phi : ℝ × ℝ → ℝ) (p : ℝ) (z : ℝ × ℝ) :
    weightedIntegrand phi p z = phi z * modelWeight p z := by
  simp [weightedIntegrand, modelWeight, div_eq_mul_inv]

private theorem weightedIntegrand_aestronglyMeasurable
    (phi : ℝ × ℝ → ℝ) (p : ℝ)
    (hcont : ContinuousOn phi disk) :
    AEStronglyMeasurable (weightedIntegrand phi p)
      (volume.restrict disk) := by
  have hphi :
      AEStronglyMeasurable phi (volume.restrict disk) :=
    hcont.aestronglyMeasurable (μ := volume) disk_measurable
  have hmodel :=
    (modelWeight_measurable p).aestronglyMeasurable
      (μ := volume.restrict disk)
  have hfun :
      weightedIntegrand phi p = phi * modelWeight p := by
    funext z
    exact weightedIntegrand_eq_mul phi p z
  rw [hfun]
  exact hphi.mul hmodel

private theorem weighted_integrable_of_model
    (phi : ℝ × ℝ → ℝ) (M p : ℝ)
    (hcont : ContinuousOn phi disk)
    (hM : ∀ z ∈ disk, |phi z| ≤ M)
    (hmodel : IntegrableOn (modelWeight p) disk volume) :
    IntegrableOn (weightedIntegrand phi p) disk volume := by
  have hM0 : 0 ≤ M :=
    (abs_nonneg (phi (0, 0))).trans (hM (0, 0) zero_mem_disk)
  apply (hmodel.const_mul M).mono'
  · exact weightedIntegrand_aestronglyMeasurable phi p hcont
  · filter_upwards [ae_restrict_mem disk_measurable] with z hz
    have hmodel0 := modelWeight_nonneg p z
    rw [weightedIntegrand_eq_mul, norm_mul, Real.norm_eq_abs,
      Real.norm_of_nonneg hmodel0]
    exact mul_le_mul_of_nonneg_right (hM z hz) hmodel0

private theorem model_integrable_of_weighted
    (phi : ℝ × ℝ → ℝ) (m p : ℝ)
    (hm0 : 0 < m)
    (hm : ∀ z ∈ disk, m ≤ |phi z|)
    (hweighted :
      IntegrableOn (weightedIntegrand phi p) disk volume) :
    IntegrableOn (modelWeight p) disk volume := by
  have hmajorant :
      Integrable
        (fun z => m⁻¹ * ‖weightedIntegrand phi p z‖)
        (volume.restrict disk) :=
    hweighted.norm.const_mul m⁻¹
  apply hmajorant.mono'
  · exact (modelWeight_measurable p).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem disk_measurable] with z hz
    have hmodel0 := modelWeight_nonneg p z
    rw [Real.norm_of_nonneg hmodel0,
      weightedIntegrand_eq_mul, norm_mul, Real.norm_eq_abs,
      Real.norm_of_nonneg hmodel0, inv_mul_eq_div]
    apply (le_div_iff₀ hm0).2
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right (hm z hz) hmodel0

private theorem segment_mem_disk
    (z : ℝ × ℝ) (hz : z ∈ disk)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (t * z.1, t * z.2) ∈ disk := by
  have ht_sq : t ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.2 ht.2)]
  have hz_nonneg : 0 ≤ z.1 ^ 2 + z.2 ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  unfold disk at hz ⊢
  change (t * z.1) ^ 2 + (t * z.2) ^ 2 ≤ 1
  calc
    (t * z.1) ^ 2 + (t * z.2) ^ 2 =
        t ^ 2 * (z.1 ^ 2 + z.2 ^ 2) := by ring
    _ ≤ 1 * (z.1 ^ 2 + z.2 ^ 2) :=
      mul_le_mul_of_nonneg_right ht_sq hz_nonneg
    _ ≤ 1 := by simpa using hz

private theorem disk_compact : IsCompact disk := by
  apply Metric.isCompact_iff_isClosed_bounded.2
  constructor
  · unfold disk
    exact isClosed_le (by fun_prop) (by fun_prop)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    intro z hz
    have hsum : z.1 ^ 2 + z.2 ^ 2 ≤ 1 := hz
    have hx : |z.1| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    have hy : |z.2| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le hx hy

private theorem exists_abs_bound_on_disk
    (phi : ℝ × ℝ → ℝ)
    (hcont : ContinuousOn phi disk) :
    ∃ M : ℝ, ∀ z ∈ disk, |phi z| ≤ M := by
  obtain ⟨M, hM⟩ :=
    disk_compact.bddAbove_image hcont.norm
  refine ⟨M, ?_⟩
  intro z hz
  have h := hM (Set.mem_image_of_mem (fun w => ‖phi w‖) hz)
  simpa [Real.norm_eq_abs] using h

private theorem phi_uniform_sign
    (phi : ℝ × ℝ → ℝ) (m : ℝ)
    (hm0 : 0 < m)
    (hcont : ContinuousOn phi disk)
    (hm : ∀ z ∈ disk, m ≤ |phi z|) :
    (∀ z ∈ disk, m ≤ phi z) ∨
      (∀ z ∈ disk, phi z ≤ -m) := by
  have hzero_abs := hm (0, 0) zero_mem_disk
  rcases (le_abs.mp hzero_abs) with hzero_pos | hzero_neg
  · left
    intro z hz
    rcases (le_abs.mp (hm z hz)) with hz_pos | hz_neg
    · exact hz_pos
    · exfalso
      let path : ℝ → ℝ × ℝ := fun t => (t * z.1, t * z.2)
      let f : ℝ → ℝ := fun t => phi (path t)
      have hpath : Continuous path := by
        unfold path
        fun_prop
      have hmaps :
          Set.MapsTo path (Set.Icc (0 : ℝ) 1) disk := by
        intro t ht
        exact segment_mem_disk z hz t ht
      have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
        exact hcont.comp hpath.continuousOn hmaps
      have hf0 : m ≤ f 0 := by
        simpa [f, path] using hzero_pos
      have hf1 : f 1 ≤ -m := by
        have hz_neg' : phi z ≤ -m := by linarith
        simpa [f, path] using hz_neg'
      have hbetween : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
        constructor <;> linarith
      obtain ⟨t, ht, hft⟩ :=
        (intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
          hfcont) hbetween
      have hpath_mem := hmaps ht
      have hzero_at_t := hm (path t) hpath_mem
      rw [show phi (path t) = 0 by
        simpa [f] using hft, abs_zero] at hzero_at_t
      linarith
  · right
    intro z hz
    rcases (le_abs.mp (hm z hz)) with hz_pos | hz_neg
    · exfalso
      let path : ℝ → ℝ × ℝ := fun t => (t * z.1, t * z.2)
      let f : ℝ → ℝ := fun t => phi (path t)
      have hpath : Continuous path := by
        unfold path
        fun_prop
      have hmaps :
          Set.MapsTo path (Set.Icc (0 : ℝ) 1) disk := by
        intro t ht
        exact segment_mem_disk z hz t ht
      have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
        exact hcont.comp hpath.continuousOn hmaps
      have hf0 : f 0 ≤ -m := by
        have hzero_neg' : phi (0, 0) ≤ -m := by linarith
        simpa [f, path] using hzero_neg'
      have hf1 : m ≤ f 1 := by
        simpa [f, path] using hz_pos
      have hbetween : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
        constructor <;> linarith
      obtain ⟨t, ht, hft⟩ :=
        (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
          hfcont) hbetween
      have hpath_mem := hmaps ht
      have hzero_at_t := hm (path t) hpath_mem
      rw [show phi (path t) = 0 by
        simpa [f] using hft, abs_zero] at hzero_at_t
      linarith
    · linarith

theorem gap7 (phi : ℝ × ℝ → ℝ) (m p : ℝ)
    (hp : p < 1) (hm0 : 0 < m)
    (hcont : ContinuousOn phi disk)
    (hm : ∀ z ∈ disk, m ≤ |phi z|) :
    m * modelIntegral p ≤ |weightedIntegral phi p| := by
  have hmodel :
      IntegrableOn (modelWeight p) disk volume :=
    (modelWeight_integrable_iff p).2 hp
  obtain ⟨M, hM⟩ := exists_abs_bound_on_disk phi hcont
  have hweighted :
      IntegrableOn (weightedIntegrand phi p) disk volume :=
    weighted_integrable_of_model phi M p hcont hM hmodel
  rcases phi_uniform_sign phi m hm0 hcont hm with hpos | hneg
  · have hminorant :
        Integrable (fun z => m * modelWeight p z)
          (volume.restrict disk) :=
      hmodel.const_mul m
    have hpoint :
        ∀ᵐ z ∂volume.restrict disk,
          m * modelWeight p z ≤ weightedIntegrand phi p z := by
      filter_upwards [ae_restrict_mem disk_measurable] with z hz
      rw [weightedIntegrand_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (hpos z hz) (modelWeight_nonneg p z)
    have hint :=
      integral_mono_ae hminorant hweighted hpoint
    change
      m * (∫ z in disk, modelWeight p z) ≤
        |∫ z in disk, weightedIntegrand phi p z|
    have hle :
        m * (∫ z in disk, modelWeight p z) ≤
          ∫ z in disk, weightedIntegrand phi p z := by
      simpa only [integral_const_mul] using hint
    exact hle.trans (le_abs_self _)
  · have hmajorant :
        Integrable (fun z => (-m) * modelWeight p z)
          (volume.restrict disk) :=
      hmodel.const_mul (-m)
    have hpoint :
        ∀ᵐ z ∂volume.restrict disk,
          weightedIntegrand phi p z ≤
            (-m) * modelWeight p z := by
      filter_upwards [ae_restrict_mem disk_measurable] with z hz
      rw [weightedIntegrand_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (hneg z hz) (modelWeight_nonneg p z)
    have hint :=
      integral_mono_ae hweighted hmajorant hpoint
    change
      m * (∫ z in disk, modelWeight p z) ≤
        |∫ z in disk, weightedIntegrand phi p z|
    have hle :
        (∫ z in disk, weightedIntegrand phi p z) ≤
          (-m) * (∫ z in disk, modelWeight p z) := by
      simpa only [integral_const_mul] using hint
    have hneg_le :
        m * (∫ z in disk, modelWeight p z) ≤
          -(∫ z in disk, weightedIntegrand phi p z) := by
      linarith
    exact hneg_le.trans (neg_le_abs _)

theorem gap8 (phi : ℝ × ℝ → ℝ) (M p : ℝ)
    (hp : p < 1)
    (hcont : ContinuousOn phi disk)
    (hM : ∀ z ∈ disk, |phi z| ≤ M) :
    |weightedIntegral phi p| ≤ M * modelIntegral p := by
  have hmodel :
      IntegrableOn (modelWeight p) disk volume :=
    (modelWeight_integrable_iff p).2 hp
  have hM0 : 0 ≤ M :=
    (abs_nonneg (phi (0, 0))).trans (hM (0, 0) zero_mem_disk)
  have hmajorant :
      Integrable (fun z => M * modelWeight p z)
        (volume.restrict disk) :=
    hmodel.const_mul M
  have hpoint :
      ∀ᵐ z ∂volume.restrict disk,
        ‖weightedIntegrand phi p z‖ ≤ M * modelWeight p z := by
    filter_upwards [ae_restrict_mem disk_measurable] with z hz
    have hmodel0 := modelWeight_nonneg p z
    rw [weightedIntegrand_eq_mul, norm_mul, Real.norm_eq_abs,
      Real.norm_of_nonneg hmodel0]
    exact mul_le_mul_of_nonneg_right (hM z hz) hmodel0
  have hbound :=
    norm_integral_le_of_norm_le hmajorant hpoint
  change
    ‖∫ z in disk, weightedIntegrand phi p z‖ ≤
      M * ∫ z in disk, modelWeight p z
  simpa only [integral_const_mul] using hbound

theorem gap9 (phi : ℝ × ℝ → ℝ) (m M p : ℝ)
    (hp : p < 1) (hm0 : 0 < m)
    (hcont : ContinuousOn phi disk)
    (hm : ∀ z ∈ disk, m ≤ |phi z|)
    (hM : ∀ z ∈ disk, |phi z| ≤ M) :
    m * modelIntegral p ≤ M * modelIntegral p := by
  exact (gap7 phi m p hp hm0 hcont hm).trans
    (gap8 phi M p hp hcont hM)

theorem gap10 (p : ℝ) (hp : p < 1) :
    modelIntegral p =
      angularIntegral p * radialIntegral p := by
  let f : ℝ × ℝ → ℝ :=
    disk.indicator (modelWeight p)
  have hpolar :=
    integral_comp_polarCoord_symm f
  calc
    modelIntegral p = ∫ z : ℝ × ℝ, f z := by
      unfold modelIntegral f
      exact (integral_indicator disk_measurable).symm
    _ = ∫ q in polarCoord.target,
        q.1 • f (polarCoord.symm q) := hpolar.symm
    _ = ∫ q in polarCoord.target,
        (Set.Iic (1 : ℝ)).indicator (radialWeight p) q.1 *
          angleWeight p q.2 := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro q hq
      have hr : 0 < q.1 := hq.1
      change
        q.1 * disk.indicator (modelWeight p)
            (polarCoord.symm (q.1, q.2)) =
          (Set.Iic (1 : ℝ)).indicator (radialWeight p) q.1 *
            angleWeight p q.2
      by_cases hr1 : q.1 ≤ 1
      · have hdisk := (polar_mem_disk_iff q.1 q.2 hr).2 hr1
        have hrmem : q.1 ∈ Set.Iic (1 : ℝ) := hr1
        rw [Set.indicator_of_mem hdisk,
          Set.indicator_of_mem hrmem]
        exact polar_model_factor p q.1 q.2 hr
      · have hdisk :
            polarCoord.symm (q.1, q.2) ∉ disk := by
          intro hdisk
          exact hr1 ((polar_mem_disk_iff q.1 q.2 hr).1 hdisk)
        have hrmem : q.1 ∉ Set.Iic (1 : ℝ) := hr1
        rw [Set.indicator_of_notMem hdisk,
          Set.indicator_of_notMem hrmem]
        simp
    _ = (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic (1 : ℝ)).indicator (radialWeight p) r) *
        ∫ theta in Set.Ioo (-Real.pi) Real.pi,
          angleWeight p theta := by
      rw [polarCoord_target, Measure.volume_eq_prod]
      exact setIntegral_prod_mul _ _ _ _
    _ = radialIntegral p * angularIntegral p := by
      rw [setIntegral_indicator measurableSet_Iic,
        angular_setIntegral_eq]
      congr 2
    _ = angularIntegral p * radialIntegral p := mul_comm _ _

theorem gap12 (phi : ℝ × ℝ → ℝ) (m M p : ℝ)
    (hm0 : 0 < m)
    (hcont : ContinuousOn phi disk)
    (hm : ∀ z ∈ disk, m ≤ |phi z|)
    (hM : ∀ z ∈ disk, |phi z| ≤ M) :
    IntegrableOn (weightedIntegrand phi p) disk ↔ p < 1 := by
  constructor
  · intro hweighted
    exact (modelWeight_integrable_iff p).1
      (model_integrable_of_weighted phi m p hm0 hm hweighted)
  · intro hp
    exact weighted_integrable_of_model phi M p hcont hM
      ((modelWeight_integrable_iff p).2 hp)

end

end ProofGap.Exercise4182
