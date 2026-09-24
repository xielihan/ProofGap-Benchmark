import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4185

noncomputable section

open MeasureTheory Set

private abbrev Point2 := ℝ × ℝ

def disk : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

def openDisk : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 < 1}

def boundaryDistance (z : ℝ × ℝ) : ℝ :=
  1 - z.1 ^ 2 - z.2 ^ 2

def modelWeight (p : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 / Real.rpow (boundaryDistance z) p

def weightedIntegrand (phi : ℝ × ℝ → ℝ) (p : ℝ)
    (z : ℝ × ℝ) : ℝ :=
  phi z / Real.rpow (boundaryDistance z) p

def modelIntegral (p : ℝ) : ℝ :=
  ∫ z in disk, modelWeight p z

def weightedIntegral (phi : ℝ × ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ z in disk, weightedIntegrand phi p z

def radialIntegral (p : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1,
    r / Real.rpow (1 - r ^ 2) p

def factoredRadialIntegral (p : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1,
    r /
      (Real.rpow (1 - r) p * Real.rpow (1 + r) p)

def normalizedRadial (p r : ℝ) : ℝ :=
  Real.rpow (1 - r) p *
    (r /
      (Real.rpow (1 - r) p * Real.rpow (1 + r) p))

def truncatedCriticalIntegral (epsilon : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1 - epsilon, r / (1 - r ^ 2)

def criticalPrimitiveAt (epsilon : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (1 - (1 - epsilon) ^ 2)

/-! Exercise 4185. -/

private theorem disk_measurable : MeasurableSet disk := by
  unfold disk
  measurability

private theorem disk_compact : IsCompact disk := by
  have hclosed : IsClosed disk := by
    exact isClosed_le (by fun_prop) (by fun_prop)
  have hbox :
      IsCompact (Icc ((-1 : ℝ), (-1 : ℝ))
        ((1 : ℝ), (1 : ℝ))) :=
    isCompact_Icc
  refine hbox.of_isClosed_subset hclosed ?_
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ 1 at hq
  have hx : |q.1| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg q.2]
  have hy : |q.2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg q.1]
  rw [mem_Icc]
  exact
    ⟨⟨(abs_le.mp hx).1, (abs_le.mp hy).1⟩,
      ⟨(abs_le.mp hx).2, (abs_le.mp hy).2⟩⟩

private def singularKernel (p t : ℝ) : ℝ :=
  1 / Real.rpow |t| p

private theorem singularKernel_eq (p t : ℝ) :
    singularKernel p t = Real.rpow |t| (-p) := by
  unfold singularKernel
  rw [one_div]
  exact (Real.rpow_neg (abs_nonneg t) p).symm

private theorem singularKernel_nonneg (p t : ℝ) :
    0 ≤ singularKernel p t := by
  rw [singularKernel_eq]
  exact Real.rpow_nonneg (abs_nonneg t) (-p)

private theorem singularKernel_measurable (p : ℝ) :
    Measurable (singularKernel p) := by
  have heq :
      singularKernel p =
        (fun t : ℝ => Real.rpow |t| (-p)) := by
    funext t
    exact singularKernel_eq p t
  rw [heq]
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  apply continuousOn_of_forall_continuousAt
  intro t ht
  simpa [Function.comp_def] using
    (Real.continuousAt_rpow_const |t| (-p)
      (Or.inl (abs_ne_zero.mpr ht))).comp continuous_abs.continuousAt

private def radialKernel (p r : ℝ) : ℝ :=
  r * singularKernel p (1 - r ^ 2)

private theorem one_sub_sq_image :
    (fun r : ℝ => 1 - r ^ 2) '' Ioc (0 : ℝ) 1 =
      Ico (0 : ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hrsq : r ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ hr.1.le zero_le_one).2 hr.2
    constructor
    · linarith
    · nlinarith [sq_pos_of_pos hr.1]
  · intro hu
    let r : ℝ := Real.sqrt (1 - u)
    have hbase : 0 < 1 - u := sub_pos.mpr hu.2
    have hrpos : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.2 hbase
    have hrsq : r ^ 2 = 1 - u := by
      dsimp [r]
      exact Real.sq_sqrt hbase.le
    have hrle : r ≤ 1 := by
      nlinarith [hu.1, sq_nonneg (r - 1)]
    refine ⟨r, ⟨hrpos, hrle⟩, ?_⟩
    nlinarith

private theorem radialKernel_integrable_iff (p : ℝ) :
    IntegrableOn (radialKernel p) (Ioc (0 : ℝ) 1) volume ↔
      p < 1 := by
  have hderiv (r : ℝ) :
      HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-2 * r) r := by
    convert (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hinj :
      InjOn (fun r : ℝ => 1 - r ^ 2) (Ioc (0 : ℝ) 1) := by
    intro r hr s hs hrs
    have hrsq : r ^ 2 = s ^ 2 := by linarith
    nlinarith [hr.1, hs.1]
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioc
      (fun r _ => (hderiv r).hasDerivWithinAt)
      hinj (singularKernel p)
  rw [one_sub_sq_image] at hchange
  have hscaled :
      IntegrableOn
          (fun r : ℝ =>
            |(-2 * r)| • singularKernel p (1 - r ^ 2))
          (Ioc (0 : ℝ) 1) volume ↔
        IntegrableOn (radialKernel p) (Ioc (0 : ℝ) 1) volume := by
    constructor
    · intro h
      have hhalf :
          IntegrableOn
            (fun r : ℝ =>
              (1 / 2 : ℝ) *
                (|(-2 * r)| • singularKernel p (1 - r ^ 2)))
            (Ioc (0 : ℝ) 1) volume := by
        exact
          (show Integrable
              (fun r : ℝ =>
                |(-2 * r)| • singularKernel p (1 - r ^ 2))
              (volume.restrict (Ioc (0 : ℝ) 1)) from h).const_mul
            (1 / 2 : ℝ)
      apply hhalf.congr_fun
      · intro r hr
        simp only [smul_eq_mul]
        rw [abs_of_neg (by nlinarith [hr.1] : -2 * r < 0)]
        simp only [radialKernel]
        ring
      · exact measurableSet_Ioc
    · intro h
      have htwo :
          IntegrableOn (fun r : ℝ => 2 * radialKernel p r)
            (Ioc (0 : ℝ) 1) volume := by
        exact
          (show Integrable (radialKernel p)
              (volume.restrict (Ioc (0 : ℝ) 1)) from h).const_mul 2
      apply htwo.congr_fun
      · intro r hr
        change 2 * radialKernel p r =
          |-2 * r| * singularKernel p (1 - r ^ 2)
        rw [abs_of_neg (by nlinarith [hr.1] : -2 * r < 0)]
        simp only [smul_eq_mul, radialKernel]
        ring
      · exact measurableSet_Ioc
  rw [← hscaled, ← hchange]
  rw [integrableOn_Ico_iff_integrableOn_Ioo]
  have hcongr :
      IntegrableOn (singularKernel p) (Ioo (0 : ℝ) 1) volume ↔
        IntegrableOn (fun t : ℝ => Real.rpow t (-p))
          (Ioo (0 : ℝ) 1) volume := by
    apply integrableOn_congr_fun
    · intro t ht
      rw [singularKernel_eq, abs_of_pos ht.1]
    · exact measurableSet_Ioo
  rw [hcongr]
  constructor
  · intro h
    have h' :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp h
    linarith
  · intro hp
    apply (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr
    linarith

private theorem integrable_polar_iff (F : Point2 → ℝ) :
    Integrable F volume ↔
      IntegrableOn
        (fun z : Point2 => z.1 * F (polarCoord.symm z))
        polarCoord.target volume := by
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := (volume : Measure Point2))
      (f := polarCoord.symm)
      (f' := fderivPolarCoordSymm)
      polarCoord.open_target.measurableSet
      (fun z _ =>
        (hasFDerivAt_polarCoord_symm z).hasFDerivWithinAt)
      polarCoord.symm.injOn F
  rw [polarCoord.symm_image_target_eq_source] at hchange
  have hsource :
      IntegrableOn F polarCoord.source volume ↔
        Integrable F volume := by
    rw [IntegrableOn,
      Measure.restrict_congr_set polarCoord_source_ae_eq_univ,
      Measure.restrict_univ]
  calc
    Integrable F volume ↔
        IntegrableOn F polarCoord.source volume :=
      hsource.symm
    _ ↔ IntegrableOn
          (fun z : Point2 =>
            |(fderivPolarCoordSymm z).det| •
              F (polarCoord.symm z))
          polarCoord.target volume :=
      hchange
    _ ↔ IntegrableOn
          (fun z : Point2 => z.1 * F (polarCoord.symm z))
          polarCoord.target volume := by
      apply integrableOn_congr_fun
      · intro z hz
        change
          |(fderivPolarCoordSymm z).det| •
              F (polarCoord.symm z) =
            z.1 * F (polarCoord.symm z)
        rw [det_fderivPolarCoordSymm,
          abs_of_pos hz.1, smul_eq_mul]
      · exact polarCoord.open_target.measurableSet

private theorem integrableOn_indicator_subset_iff
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s t : Set α} {F : α → ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) :
    IntegrableOn (s.indicator F) t μ ↔
      IntegrableOn F s μ := by
  constructor
  · intro h
    have hi := h.integrable_indicator ht
    have heq :
        t.indicator (s.indicator F) = s.indicator F := by
      funext x
      by_cases hx : x ∈ s
      · simp [hx, hst hx]
      · simp [hx]
    rw [heq] at hi
    exact (integrable_indicator_iff hs).mp hi
  · intro h
    exact (h.integrable_indicator hs).integrableOn

private def polarRectangle : Set Point2 :=
  Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi

private theorem polarRectangle_measurable :
    MeasurableSet polarRectangle :=
  measurableSet_Ioc.prod measurableSet_Ioo

private theorem polarRectangle_subset_target :
    polarRectangle ⊆ polarCoord.target := by
  intro z hz
  exact ⟨hz.1.1, hz.2⟩

private def modelProduct (p : ℝ) (q : Point2) : ℝ :=
  disk.indicator
    (fun q =>
      singularKernel p (1 - q.1 ^ 2 - q.2 ^ 2)) q

private theorem modelProduct_measurable (p : ℝ) :
    Measurable (modelProduct p) := by
  unfold modelProduct
  exact
    ((singularKernel_measurable p).comp
      (measurable_const.sub (measurable_fst.pow_const 2) |>.sub
        (measurable_snd.pow_const 2))).indicator disk_measurable

private theorem modelProduct_nonneg (p : ℝ) (q : Point2) :
    0 ≤ modelProduct p q := by
  unfold modelProduct
  by_cases hq : q ∈ disk
  · rw [indicator_of_mem hq]
    exact singularKernel_nonneg _ _
  · rw [indicator_of_notMem hq]

private theorem polar_model_eq (p : ℝ) :
    EqOn
      (fun z : Point2 =>
        z.1 * modelProduct p (polarCoord.symm z))
      (polarRectangle.indicator
        (fun z : Point2 => radialKernel p z.1))
      polarCoord.target := by
  intro z hz
  have hr : 0 < z.1 := hz.1
  have hang : z.2 ∈ Ioo (-Real.pi) Real.pi := hz.2
  have hnorm :
      (polarCoord.symm z).1 ^ 2 +
          (polarCoord.symm z).2 ^ 2 =
        z.1 ^ 2 := by
    simp only [polarCoord_symm_apply]
    rw [mul_pow, mul_pow, ← mul_add,
      Real.cos_sq_add_sin_sq, mul_one]
  by_cases hr1 : z.1 ≤ 1
  · have hdisk : polarCoord.symm z ∈ disk := by
      change
        (polarCoord.symm z).1 ^ 2 +
            (polarCoord.symm z).2 ^ 2 ≤ 1
      rw [hnorm]
      nlinarith
    have hrect : z ∈ polarRectangle :=
      ⟨⟨hr, hr1⟩, hang⟩
    simp only [modelProduct]
    rw [indicator_of_mem hdisk,
      indicator_of_mem hrect]
    simp only [radialKernel]
    congr 2
    linarith [hnorm]
  · have hdisk : polarCoord.symm z ∉ disk := by
      intro hdisk
      apply hr1
      change
        (polarCoord.symm z).1 ^ 2 +
            (polarCoord.symm z).2 ^ 2 ≤ 1 at hdisk
      rw [hnorm] at hdisk
      nlinarith
    have hrect : z ∉ polarRectangle := by
      intro h
      exact hr1 h.1.2
    simp only [modelProduct]
    rw [indicator_of_notMem hdisk,
      indicator_of_notMem hrect, mul_zero]

private theorem radial_prod_integrable_iff (p : ℝ) :
    IntegrableOn (fun z : Point2 => radialKernel p z.1)
        polarRectangle volume ↔
      IntegrableOn (radialKernel p) (Ioc (0 : ℝ) 1) volume := by
  have hangleVol :
      (volume : Measure ℝ) (Ioo (-Real.pi) Real.pi) ≠ 0 := by
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_ne_zero_iff.mpr
    linarith [Real.pi_pos]
  have hangleNe :
      (volume : Measure ℝ).restrict
          (Ioo (-Real.pi) Real.pi) ≠ 0 := by
    exact mt Measure.restrict_eq_zero.mp hangleVol
  have hiff :=
    Integrable.comp_fst_iff
      (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))
      (ν := (volume : Measure ℝ).restrict
        (Ioo (-Real.pi) Real.pi))
      (f := radialKernel p) hangleNe
  simpa only [IntegrableOn, polarRectangle,
    Measure.volume_eq_prod, ← Measure.prod_restrict] using hiff

private theorem modelProduct_integrable_iff (p : ℝ) :
    Integrable (modelProduct p) volume ↔ p < 1 := by
  calc
    Integrable (modelProduct p) volume ↔
        IntegrableOn
          (fun z : Point2 =>
            z.1 * modelProduct p (polarCoord.symm z))
          polarCoord.target volume :=
      integrable_polar_iff (modelProduct p)
    _ ↔ IntegrableOn
          (polarRectangle.indicator
            (fun z : Point2 => radialKernel p z.1))
          polarCoord.target volume := by
      apply integrableOn_congr_fun
      · exact polar_model_eq p
      · exact polarCoord.open_target.measurableSet
    _ ↔ IntegrableOn
          (fun z : Point2 => radialKernel p z.1)
          polarRectangle volume :=
      integrableOn_indicator_subset_iff
        polarRectangle_measurable
        polarCoord.open_target.measurableSet
        polarRectangle_subset_target
    _ ↔ IntegrableOn (radialKernel p)
          (Ioc (0 : ℝ) 1) volume :=
      radial_prod_integrable_iff p
    _ ↔ p < 1 :=
      radialKernel_integrable_iff p

private theorem integrand_integrable_of_lt
    (φ : Point2 → ℝ) (p : ℝ)
    (hφ : ContinuousOn φ disk)
    (hbounded : ∃ M : ℝ, ∀ q ∈ disk, |φ q| ≤ M)
    (hp : p < 1) :
    IntegrableOn (weightedIntegrand φ p) disk volume := by
  rcases hbounded with ⟨M, hM⟩
  let D : ℝ := max M 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hDφ : ∀ q ∈ disk, |φ q| ≤ D := by
    intro q hq
    exact (hM q hq).trans (le_max_left _ _)
  have hmodel :
      Integrable (modelProduct p) volume :=
    (modelProduct_integrable_iff p).mpr hp
  have hφind :
      AEStronglyMeasurable (disk.indicator φ) volume := by
    apply (aestronglyMeasurable_indicator_iff disk_measurable).mpr
    exact hφ.aestronglyMeasurable disk_measurable
  have hφindBound :
      ∀ᵐ q ∂(volume : Measure Point2),
        ‖disk.indicator φ q‖ ≤ D := by
    filter_upwards with q
    by_cases hq : q ∈ disk
    · rw [indicator_of_mem hq, Real.norm_eq_abs]
      exact hDφ q hq
    · rw [indicator_of_notMem hq, norm_zero]
      exact hD0
  have hweighted :
      Integrable
        (fun q : Point2 =>
          disk.indicator φ q * modelProduct p q)
        volume :=
    hmodel.bdd_mul hφind hφindBound
  have heq :
      disk.indicator (weightedIntegrand φ p) =
        (fun q : Point2 =>
          disk.indicator φ q * modelProduct p q) := by
    funext q
    by_cases hq : q ∈ disk
    · have hu :
          0 ≤ 1 - q.1 ^ 2 - q.2 ^ 2 := by
        change q.1 ^ 2 + q.2 ^ 2 ≤ 1 at hq
        linarith
      rw [indicator_of_mem hq, indicator_of_mem hq]
      simp only [modelProduct, indicator_of_mem hq,
        weightedIntegrand, boundaryDistance, singularKernel, abs_of_nonneg hu,
        div_eq_mul_inv, one_mul]
    · rw [indicator_of_notMem hq, indicator_of_notMem hq]
      simp only [modelProduct, indicator_of_notMem hq, zero_mul]
  apply (integrable_indicator_iff disk_measurable).mp
  rw [heq]
  exact hweighted

private theorem integrand_integrable_implies_lt
    (φ : Point2 → ℝ) (p m : ℝ)
    (hφ : ContinuousOn φ disk)
    (hm0 : 0 < m)
    (hm : ∀ q ∈ disk, m ≤ |φ q|)
    (hint : IntegrableOn (weightedIntegrand φ p) disk volume) :
    p < 1 := by
  have hweighted :
      Integrable (disk.indicator (weightedIntegrand φ p)) volume :=
    (integrable_indicator_iff disk_measurable).mpr hint
  have hφne : ∀ q ∈ disk, φ q ≠ 0 := by
    intro q hq hzero
    have h := hm q hq
    rw [hzero, abs_zero] at h
    linarith
  have hinvCont :
      ContinuousOn (fun q : Point2 => 1 / φ q) disk := by
    exact continuousOn_const.div hφ hφne
  have hinvMeas :
      AEStronglyMeasurable
        (disk.indicator (fun q : Point2 => 1 / φ q))
        volume := by
    apply (aestronglyMeasurable_indicator_iff disk_measurable).mpr
    exact hinvCont.aestronglyMeasurable disk_measurable
  have hinvBound :
      ∀ᵐ q ∂(volume : Measure Point2),
        ‖disk.indicator (fun q : Point2 => 1 / φ q) q‖ ≤
          1 / m := by
    filter_upwards with q
    by_cases hq : q ∈ disk
    · rw [indicator_of_mem hq, Real.norm_eq_abs, abs_div,
          abs_one]
      exact one_div_le_one_div_of_le hm0 (hm q hq)
    · rw [indicator_of_notMem hq, norm_zero]
      positivity
  have hcancelled :
      Integrable
        (fun q : Point2 =>
          disk.indicator (fun q : Point2 => 1 / φ q) q *
            disk.indicator (weightedIntegrand φ p) q)
        volume :=
    hweighted.bdd_mul hinvMeas hinvBound
  have hmodel : Integrable (modelProduct p) volume := by
    convert hcancelled using 1
    funext q
    by_cases hq : q ∈ disk
    · have hu :
          0 ≤ 1 - q.1 ^ 2 - q.2 ^ 2 := by
        change q.1 ^ 2 + q.2 ^ 2 ≤ 1 at hq
        linarith
      simp only [modelProduct, indicator_of_mem hq,
        weightedIntegrand, boundaryDistance, singularKernel, abs_of_nonneg hu]
      rw [← mul_div_assoc, one_div_mul_cancel (hφne q hq)]
    · simp only [modelProduct, indicator_of_notMem hq, zero_mul]
  exact (modelProduct_integrable_iff p).mp hmodel

private theorem zero_mem_disk : (0, 0) ∈ disk := by
  norm_num [disk]

private theorem openDisk_subset_disk : openDisk ⊆ disk := by
  intro z hz
  change z.1 ^ 2 + z.2 ^ 2 < 1 at hz
  change z.1 ^ 2 + z.2 ^ 2 ≤ 1
  exact le_of_lt hz

private theorem boundaryDistance_pos {z : ℝ × ℝ}
    (hz : z ∈ openDisk) :
    0 < boundaryDistance z := by
  change z.1 ^ 2 + z.2 ^ 2 < 1 at hz
  unfold boundaryDistance
  linarith

private theorem boundaryDistance_nonneg {z : ℝ × ℝ}
    (hz : z ∈ disk) :
    0 ≤ boundaryDistance z := by
  change z.1 ^ 2 + z.2 ^ 2 ≤ 1 at hz
  unfold boundaryDistance
  linarith

private theorem modelWeight_nonneg (p : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ disk) :
    0 ≤ modelWeight p z := by
  unfold modelWeight
  exact one_div_nonneg.mpr
    (Real.rpow_nonneg (boundaryDistance_nonneg hz) p)

private theorem weightedIntegrand_eq_mul
    (phi : ℝ × ℝ → ℝ) (p : ℝ) (z : ℝ × ℝ) :
    weightedIntegrand phi p z = phi z * modelWeight p z := by
  simp [weightedIntegrand, modelWeight, div_eq_mul_inv]

private theorem modelWeight_integrable_iff (p : ℝ) :
    IntegrableOn (modelWeight p) disk ↔ p < 1 := by
  rw [← modelProduct_integrable_iff p,
    ← integrable_indicator_iff disk_measurable]
  have heq :
      disk.indicator (modelWeight p) = modelProduct p := by
    funext z
    by_cases hz : z ∈ disk
    · have hu := boundaryDistance_nonneg hz
      have hu' : 0 ≤ 1 - z.1 ^ 2 - z.2 ^ 2 := by
        simpa [boundaryDistance] using hu
      simp [modelProduct, modelWeight, boundaryDistance,
        singularKernel, hz, abs_of_nonneg hu']
    · simp [modelProduct, hz]
  rw [heq]

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

private theorem modelIntegral_eq_two_pi_radial
    (p : ℝ) (hp : p < 1) :
    modelIntegral p = 2 * Real.pi * radialIntegral p := by
  let f : ℝ × ℝ → ℝ := modelProduct p
  have hpolar := integral_comp_polarCoord_symm f
  have hmodel :
      modelIntegral p = ∫ q : ℝ × ℝ, f q := by
    unfold modelIntegral f
    rw [← integral_indicator disk_measurable]
    apply integral_congr_ae
    filter_upwards with q
    by_cases hq : q ∈ disk
    · have hu := boundaryDistance_nonneg hq
      have hu' : 0 ≤ 1 - q.1 ^ 2 - q.2 ^ 2 := by
        simpa [boundaryDistance] using hu
      simp [modelProduct, modelWeight, boundaryDistance,
        singularKernel, hq, abs_of_nonneg hu']
    · simp [modelProduct, hq]
  have hrad :
      (∫ r in Set.Ioc (0 : ℝ) 1, radialKernel p r) =
        radialIntegral p := by
    unfold radialIntegral
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have hu : 0 ≤ 1 - r ^ 2 := by
      nlinarith [mul_nonneg hr.1.le (sub_nonneg.mpr hr.2)]
    simp [radialKernel, singularKernel, abs_of_nonneg hu,
      div_eq_mul_inv]
  have hang :
      (∫ theta in Set.Ioo (-Real.pi) Real.pi,
          (1 : ℝ)) = 2 * Real.pi := by
    have hpi : -Real.pi ≤ Real.pi := by
      linarith [Real.pi_pos]
    calc
      (∫ theta in Set.Ioo (-Real.pi) Real.pi,
          (1 : ℝ)) =
          ∫ theta in (-Real.pi)..Real.pi, (1 : ℝ) := by
        rw [intervalIntegral.integral_of_le hpi]
        exact setIntegral_congr_set Ioo_ae_eq_Ioc
      _ = 2 * Real.pi := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  calc
    modelIntegral p = ∫ q : ℝ × ℝ, f q := hmodel
    _ = ∫ q in polarCoord.target,
        q.1 • f (polarCoord.symm q) := hpolar.symm
    _ = ∫ q in polarCoord.target,
        (Set.Iic (1 : ℝ)).indicator (radialKernel p) q.1 *
          (fun _ : ℝ => 1) q.2 := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro q hq
      change
        q.1 * modelProduct p (polarCoord.symm q) =
          (Set.Iic (1 : ℝ)).indicator (radialKernel p) q.1 * 1
      have heq :
          q.1 * modelProduct p (polarCoord.symm q) =
            polarRectangle.indicator
              (fun z : ℝ × ℝ => radialKernel p z.1) q :=
        polar_model_eq p hq
      rw [heq]
      by_cases hr1 : q.1 ≤ 1
      · have hrect : q ∈ polarRectangle :=
          ⟨⟨hq.1, hr1⟩, hq.2⟩
        simp [hrect, hr1]
      · have hrect : q ∉ polarRectangle := by
          intro h
          exact hr1 h.1.2
        simp [hrect, hr1]
    _ = (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic (1 : ℝ)).indicator (radialKernel p) r) *
        ∫ theta in Set.Ioo (-Real.pi) Real.pi,
          (fun _ : ℝ => 1) theta := by
      rw [polarCoord_target, Measure.volume_eq_prod]
      simpa only using
        (setIntegral_prod_mul
          (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))
          ((Set.Iic (1 : ℝ)).indicator (radialKernel p))
          (fun _ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi))
    _ = radialIntegral p * (2 * Real.pi) := by
      have hset :
          Set.Ioi (0 : ℝ) ∩ Set.Iic 1 =
            Set.Ioc (0 : ℝ) 1 := by
        ext r
        simp
      rw [setIntegral_indicator measurableSet_Iic,
        hset, hrad, hang]
    _ = 2 * Real.pi * radialIntegral p := by ring

private theorem originalProblem
    (φ : Point2 → ℝ) (p : ℝ)
    (hφ : ContinuousOn φ disk)
    (hbounded : ∃ M : ℝ, ∀ q ∈ disk, |φ q| ≤ M) :
    (p < 1 →
      IntegrableOn (weightedIntegrand φ p) disk MeasureTheory.volume) ∧
    ((∃ m > 0, ∀ q ∈ disk, m ≤ |φ q|) →
      (IntegrableOn (weightedIntegrand φ p) disk MeasureTheory.volume ↔ p < 1)) := by
  constructor
  · intro hp
    exact integrand_integrable_of_lt φ p hφ hbounded hp
  · rintro ⟨m, hm0, hm⟩
    constructor
    · intro hint
      exact integrand_integrable_implies_lt φ p m hφ hm0 hm hint
    · intro hp
      exact integrand_integrable_of_lt φ p hφ hbounded hp

theorem gap1 (phi : ℝ × ℝ → ℝ) (m p : ℝ)
    (z : ℝ × ℝ) (hz : z ∈ openDisk)
    (hm : ∀ w ∈ disk, m ≤ |phi w|) :
    m / Real.rpow (boundaryDistance z) p ≤
      |phi z| / Real.rpow (boundaryDistance z) p := by
  exact div_le_div_of_nonneg_right
    (hm z (openDisk_subset_disk hz))
    (Real.rpow_pos_of_pos (boundaryDistance_pos hz) p).le

theorem gap2 (phi : ℝ × ℝ → ℝ) (M p : ℝ)
    (z : ℝ × ℝ) (hz : z ∈ openDisk)
    (hM : ∀ w ∈ disk, |phi w| ≤ M) :
    |phi z| / Real.rpow (boundaryDistance z) p ≤
      M / Real.rpow (boundaryDistance z) p := by
  exact div_le_div_of_nonneg_right
    (hM z (openDisk_subset_disk hz))
    (Real.rpow_pos_of_pos (boundaryDistance_pos hz) p).le

theorem gap3 (phi : ℝ × ℝ → ℝ) (m M p : ℝ)
    (z : ℝ × ℝ) (hz : z ∈ openDisk)
    (hm : ∀ w ∈ disk, m ≤ |phi w|)
    (hM : ∀ w ∈ disk, |phi w| ≤ M) :
    m / Real.rpow (boundaryDistance z) p ≤
      M / Real.rpow (boundaryDistance z) p :=
  (gap1 phi m p z hz hm).trans
    (gap2 phi M p z hz hM)

theorem gap4 (phi : ℝ × ℝ → ℝ) (m p : ℝ)
    (hp : p < 1) (hm0 : 0 < m)
    (hcont : ContinuousOn phi disk)
    (hm : ∀ z ∈ disk, m ≤ |phi z|) :
    m * modelIntegral p ≤ |weightedIntegral phi p| := by
  have hmodel :
      IntegrableOn (modelWeight p) disk :=
    (modelWeight_integrable_iff p).2 hp
  obtain ⟨M, hM⟩ := exists_abs_bound_on_disk phi hcont
  have hweighted :
      IntegrableOn (weightedIntegrand phi p) disk :=
    integrand_integrable_of_lt phi p hcont ⟨M, hM⟩ hp
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
        (hpos z hz) (modelWeight_nonneg p hz)
    have hint := integral_mono_ae hminorant hweighted hpoint
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
        (hneg z hz) (modelWeight_nonneg p hz)
    have hint := integral_mono_ae hweighted hmajorant hpoint
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

theorem gap5 (phi : ℝ × ℝ → ℝ) (M p : ℝ)
    (hp : p < 1)
    (hM : ∀ z ∈ disk, |phi z| ≤ M) :
    |weightedIntegral phi p| ≤ M * modelIntegral p := by
  have hmodel :
      IntegrableOn (modelWeight p) disk :=
    (modelWeight_integrable_iff p).2 hp
  have hmajorant :
      Integrable (fun z => M * modelWeight p z)
        (volume.restrict disk) :=
    hmodel.const_mul M
  have hpoint :
      ∀ᵐ z ∂volume.restrict disk,
        ‖weightedIntegrand phi p z‖ ≤ M * modelWeight p z := by
    filter_upwards [ae_restrict_mem disk_measurable] with z hz
    have hmodel0 := modelWeight_nonneg p hz
    rw [weightedIntegrand_eq_mul, norm_mul, Real.norm_eq_abs,
      Real.norm_of_nonneg hmodel0]
    exact mul_le_mul_of_nonneg_right (hM z hz) hmodel0
  have hbound := norm_integral_le_of_norm_le hmajorant hpoint
  change
    |∫ z in disk, weightedIntegrand phi p z| ≤
      M * ∫ z in disk, modelWeight p z
  simpa only [integral_const_mul, Real.norm_eq_abs] using hbound

theorem gap6 (phi : ℝ × ℝ → ℝ) (m M p : ℝ)
    (hp : p < 1) (hm0 : 0 < m)
    (hcont : ContinuousOn phi disk)
    (hm : ∀ z ∈ disk, m ≤ |phi z|)
    (hM : ∀ z ∈ disk, |phi z| ≤ M) :
    m * modelIntegral p ≤ M * modelIntegral p :=
  (gap4 phi m p hp hm0 hcont hm).trans
    (gap5 phi M p hp hM)

theorem gap7 (p : ℝ) (hp : p < 1) :
    modelIntegral p =
      ∫ theta in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          r / Real.rpow (1 - r ^ 2) p := by
  rw [modelIntegral_eq_two_pi_radial p hp]
  change
    2 * Real.pi * radialIntegral p =
      ∫ theta in (0 : ℝ)..2 * Real.pi, radialIntegral p
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem gap8 (p : ℝ) (hp : p < 1) :
    (∫ theta in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          r / Real.rpow (1 - r ^ 2) p) =
      2 * Real.pi * factoredRadialIntegral p := by
  have hrad :
      radialIntegral p = factoredRadialIntegral p := by
    unfold radialIntegral factoredRadialIntegral
    rw [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have hminus : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
    have hplus : 0 ≤ 1 + r := by linarith [hr.1]
    change
      r / Real.rpow (1 - r ^ 2) p =
        r / (Real.rpow (1 - r) p * Real.rpow (1 + r) p)
    rw [show 1 - r ^ 2 = (1 - r) * (1 + r) by ring]
    have hpow :
        Real.rpow ((1 - r) * (1 + r)) p =
          Real.rpow (1 - r) p * Real.rpow (1 + r) p :=
      Real.mul_rpow hminus hplus
    rw [hpow]
  change
    (∫ theta in (0 : ℝ)..2 * Real.pi, radialIntegral p) =
      2 * Real.pi * factoredRadialIntegral p
  rw [intervalIntegral.integral_const, hrad]
  simp only [sub_zero, smul_eq_mul]

theorem gap9 (p : ℝ) (hp : p < 1) :
    modelIntegral p =
      2 * Real.pi * factoredRadialIntegral p :=
  (gap7 p hp).trans (gap8 p hp)

theorem gap10 (p : ℝ) :
    Tendsto (normalizedRadial p)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (Real.rpow 2 (-p))) := by
  let F : Filter ℝ := nhdsWithin (1 : ℝ) (Set.Iio 1)
  let g : ℝ → ℝ :=
    fun r => r / Real.rpow (1 + r) p
  have hbase :
      ContinuousAt (fun r : ℝ => 1 + r) 1 :=
    continuousAt_const.add continuousAt_id
  have hden :
      ContinuousAt (fun r : ℝ => Real.rpow (1 + r) p) 1 := by
    exact
      (Real.continuousAt_rpow_const (1 + 1) p
        (Or.inl (by norm_num))).comp hbase
  have hden_ne : Real.rpow (1 + (1 : ℝ)) p ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) p).ne'
  have hg :
      Tendsto g (nhds (1 : ℝ))
        (nhds ((1 : ℝ) / Real.rpow 2 p)) := by
    have hc :
        ContinuousAt
          (fun r : ℝ => r / Real.rpow (1 + r) p) 1 :=
      (show ContinuousAt (fun r : ℝ => r) 1 from
        continuousAt_id).div hden hden_ne
    change
      Tendsto (fun r : ℝ => r / Real.rpow (1 + r) p)
        (nhds (1 : ℝ))
        (nhds ((1 : ℝ) / Real.rpow 2 p))
    unfold ContinuousAt at hc
    convert hc using 1 <;> norm_num [one_div]
  have hgF :
      Tendsto g F
        (nhds ((1 : ℝ) / Real.rpow 2 p)) :=
    hg.mono_left inf_le_left
  have hgt : ∀ᶠ r in F, 0 < r := by
    exact
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        inf_le_left
  have heq :
      normalizedRadial p =ᶠ[F] g := by
    filter_upwards [self_mem_nhdsWithin, hgt] with r hr hr0
    have hminus : 0 < 1 - r := sub_pos.mpr hr
    have hplus : 0 < 1 + r := by linarith
    have hminusPow :
        Real.rpow (1 - r) p ≠ 0 :=
      (Real.rpow_pos_of_pos hminus p).ne'
    have hplusPow :
        Real.rpow (1 + r) p ≠ 0 :=
      (Real.rpow_pos_of_pos hplus p).ne'
    unfold normalizedRadial g
    field_simp [hminusPow, hplusPow]
  have hlim :
      (1 : ℝ) / Real.rpow 2 p =
        Real.rpow 2 (-p) := by
    simpa only [one_div] using
      (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) p).symm
  rw [← hlim]
  exact hgF.congr' heq.symm

theorem gap11 (epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    truncatedCriticalIntegral epsilon =
      criticalPrimitiveAt epsilon := by
  let b : ℝ := 1 - epsilon
  let G : ℝ → ℝ :=
    fun r => -(1 / 2 : ℝ) * Real.log (1 - r ^ 2)
  have hb0 : 0 ≤ b := by
    dsimp [b]
    linarith
  have hb1 : b < 1 := by
    dsimp [b]
    linarith
  have hden (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) b) :
      1 - r ^ 2 ≠ 0 := by
    have hr1 : r < 1 := hr.2.trans_lt hb1
    have : 0 < 1 - r ^ 2 := by
      nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
    exact this.ne'
  have hderiv (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) b) :
      HasDerivAt G (r / (1 - r ^ 2)) r := by
    have hinner :
        HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
      convert
        (hasDerivAt_const r (1 : ℝ)).sub
          ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hlog :=
      (Real.hasDerivAt_log (hden r hr)).comp r hinner
    unfold G
    convert hlog.const_mul (-(1 / 2 : ℝ)) using 1 <;>
      field_simp [hden r hr] <;> ring
  have hcont :
      ContinuousOn (fun r : ℝ => r / (1 - r ^ 2))
        (Set.uIcc (0 : ℝ) b) := by
    rw [Set.uIcc_of_le hb0]
    intro r hr
    have hnum :
        ContinuousAt (fun x : ℝ => x) r :=
      continuousAt_id
    have hdenCont :
        ContinuousAt (fun x : ℝ => 1 - x ^ 2) r :=
      continuousAt_const.sub (continuousAt_id.pow 2)
    exact
      (hnum.div hdenCont (hden r hr)).continuousWithinAt
  have hFTC :
      (∫ r in (0 : ℝ)..b, r / (1 - r ^ 2)) =
        G b - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => by
        rw [Set.uIcc_of_le hb0] at hr
        exact hderiv r hr)
      hcont.intervalIntegrable
  unfold truncatedCriticalIntegral criticalPrimitiveAt
  change
    (∫ r in (0 : ℝ)..b, r / (1 - r ^ 2)) =
      -(1 / 2 : ℝ) * Real.log (1 - b ^ 2)
  rw [hFTC]
  simp [G]

theorem gap12 :
    Tendsto criticalPrimitiveAt
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let u : ℝ → ℝ :=
    fun epsilon => 1 - (1 - epsilon) ^ 2
  have hu0 :
      Tendsto u F (nhds (0 : ℝ)) := by
    have hc : ContinuousAt u 0 := by
      unfold u
      fun_prop
    unfold ContinuousAt at hc
    convert hc.mono_left inf_le_left using 1 <;>
      norm_num [u]
  have hepsilon1 : ∀ᶠ epsilon in F, epsilon < 1 := by
    exact
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        inf_le_left
  have hupos : ∀ᶠ epsilon in F, 0 < u epsilon := by
    filter_upwards [self_mem_nhdsWithin, hepsilon1] with
      epsilon hepsilon0 hepsilon1
    change 0 < 1 - (1 - epsilon) ^ 2
    nlinarith [mul_pos hepsilon0 (sub_pos.mpr hepsilon1)]
  have humap :
      Tendsto u F (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu0, hupos⟩
  have hlog :
      Tendsto (fun epsilon => Real.log (u epsilon))
        F atBot :=
    Real.tendsto_log_nhdsGT_zero.comp humap
  refine Filter.tendsto_atTop.2 ?_
  intro B
  filter_upwards [(Filter.tendsto_atBot.1 hlog) (-2 * B)] with
    epsilon hepsilon
  unfold u at hepsilon
  unfold criticalPrimitiveAt
  nlinarith

theorem gap13 :
    Tendsto truncatedCriticalIntegral
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hepsilon1 : ∀ᶠ epsilon in F, epsilon < 1 := by
    exact
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        inf_le_left
  have heq :
      truncatedCriticalIntegral =ᶠ[F] criticalPrimitiveAt := by
    filter_upwards [self_mem_nhdsWithin, hepsilon1] with
      epsilon hepsilon0 hepsilon1
    exact gap11 epsilon hepsilon0 hepsilon1
  exact gap12.congr' heq.symm

theorem gap14 (phi : ℝ × ℝ → ℝ) (m p : ℝ)
    (hm0 : 0 < m)
    (hcont : ContinuousOn phi disk)
    (hm : ∀ z ∈ disk, m ≤ |phi z|) :
    IntegrableOn (weightedIntegrand phi p) disk ↔
      p < 1 := by
  constructor
  · intro hweighted
    exact
      integrand_integrable_implies_lt
        phi p m hcont hm0 hm hweighted
  · intro hp
    obtain ⟨M, hM⟩ :=
      exists_abs_bound_on_disk phi hcont
    exact
      integrand_integrable_of_lt
        phi p hcont ⟨M, hM⟩ hp

end

end ProofGap.Exercise4185
