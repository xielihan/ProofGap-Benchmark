import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise4184

noncomputable section

open MeasureTheory Set

private abbrev Point2 := ℝ × ℝ

def square (a : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ a ∧ 0 ≤ z.2 ∧ z.2 ≤ a}

def modelKernel (p x y : ℝ) : ℝ :=
  1 / Real.rpow |x - y| p

def weightedKernel (phi : ℝ × ℝ → ℝ) (p x y : ℝ) : ℝ :=
  phi (x, y) / Real.rpow |x - y| p

private def weightedKernelOnPoint
    (φ : Point2 → ℝ) (p : ℝ) (q : Point2) : ℝ :=
  weightedKernel φ p q.1 q.2

def modelIntegral (a p : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..a, modelKernel p x y

def weightedIntegral (phi : ℝ × ℝ → ℝ) (a p : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..a, weightedKernel phi p x y

def lowerTriangleIntegral (a p : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..x, modelKernel p x y

def powerIntegral (a p : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, Real.rpow x (1 - p) / (1 - p)

def truncatedIntegral (a p epsilon : ℝ) : ℝ :=
  ∫ x in epsilon..a,
    ∫ y in (0 : ℝ)..x - epsilon, modelKernel p x y

def logarithmicExpression (a epsilon : ℝ) : ℝ :=
  a * Real.log a - a + epsilon - a * Real.log epsilon

/-! Exercise 4184. -/

private theorem square_eq_prod (a : ℝ) :
    square a = Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
  ext q
  simp only [square, mem_setOf_eq, mem_prod, mem_Icc]
  aesop

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

private theorem singularKernel_intervalIntegrable
    (p c d : ℝ) (hp : p < 1) :
    IntervalIntegrable (singularKernel p) volume c d := by
  let R : ℝ := max |c| |d| + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hs : -1 < -p := by linarith
  have hbase :
      IntervalIntegrable (fun t : ℝ => Real.rpow t (-p))
        volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' hs
  have hpos :
      IntervalIntegrable (singularKernel p) volume 0 R := by
    apply hbase.congr
    intro t ht
    have ht' : t ∈ Ioc 0 R := by
      simpa [uIoc_of_le hR.le] using ht
    rw [singularKernel_eq, abs_of_nonneg ht'.1.le]
  have hnegBase :
      IntervalIntegrable
        (fun t : ℝ => Real.rpow (-t) (-p))
        volume (-R) 0 := by
    have h :=
      (IntervalIntegrable.iff_comp_neg
        (f := fun t : ℝ => Real.rpow t (-p))).mp hbase
    simpa using h.symm
  have hneg :
      IntervalIntegrable (singularKernel p) volume (-R) 0 := by
    apply hnegBase.congr
    intro t ht
    have ht' : t ∈ Ioc (-R) 0 := by
      simpa [uIoc_of_le (neg_nonpos.mpr hR.le)] using ht
    rw [singularKernel_eq, abs_of_nonpos ht'.2]
  have hfull :
      IntervalIntegrable (singularKernel p) volume (-R) R :=
    hneg.trans hpos
  apply hfull.mono_set'
  intro t ht
  have hcR : |c| < R := by
    dsimp [R]
    linarith [le_max_left |c| |d|]
  have hdR : |d| < R := by
    dsimp [R]
    linarith [le_max_right |c| |d|]
  have hcL : -R < c := (neg_lt_neg hcR).trans_le (neg_abs_le c)
  have hdL : -R < d := (neg_lt_neg hdR).trans_le (neg_abs_le d)
  have hcU : c < R := (le_abs_self c).trans_lt hcR
  have hdU : d < R := (le_abs_self d).trans_lt hdR
  rw [uIoc_of_le (neg_le_self hR.le)]
  rw [mem_uIoc] at ht
  rcases ht with ⟨hct, htd⟩ | ⟨hdt, htc⟩
  · exact ⟨hcL.trans hct, htd.trans hdU.le⟩
  · exact ⟨hdL.trans hdt, htc.trans hcU.le⟩

private def modelProduct (p a : ℝ) (q : Point2) : ℝ :=
  (Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a).indicator
    (fun q => singularKernel p (q.1 - q.2)) q

private theorem modelProduct_measurable (p a : ℝ) :
    Measurable (modelProduct p a) := by
  unfold modelProduct
  exact
    ((singularKernel_measurable p).comp
      (measurable_fst.sub measurable_snd)).indicator
        (measurableSet_Icc.prod measurableSet_Icc)

private theorem modelProduct_integrable
    (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    Integrable (modelProduct p a)
      ((volume : Measure ℝ).prod volume) := by
  have hmeas :
      AEStronglyMeasurable (modelProduct p a)
        ((volume : Measure ℝ).prod volume) :=
    (modelProduct_measurable p a).aestronglyMeasurable
  let R : ℝ := |a| + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hbigInterval :
      IntervalIntegrable (singularKernel p) volume (-R) R :=
    singularKernel_intervalIntegrable p (-R) R hp
  have hbig :
      IntegrableOn (singularKernel p) (Icc (-R) R) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (neg_le_self hR.le)).mp hbigInterval
  let K : ℝ :=
    ∫ t in Icc (-R) R, singularKernel p t
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun t =>
        singularKernel_nonneg p t)
  have hsections :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Integrable (fun y : ℝ => modelProduct p a (x, y)) volume := by
    filter_upwards with x
    by_cases hx : x ∈ Icc (0 : ℝ) a
    · have hshift :
          IntervalIntegrable
            (fun y : ℝ => singularKernel p (x - y))
            volume 0 a := by
        have h :=
          (singularKernel_intervalIntegrable p (x - a) x hp).comp_sub_left x
        simpa using h.symm
      have hi :
          Integrable
            ((Icc (0 : ℝ) a).indicator
              (fun y : ℝ => singularKernel p (x - y)))
            volume :=
        (integrable_indicator_iff measurableSet_Icc).mpr
          ((intervalIntegrable_iff_integrableOn_Icc_of_le
            ha.le).mp hshift)
      convert hi using 1
      funext y
      by_cases hy : y ∈ Icc (0 : ℝ) a
      · have hxy :
            (x, y) ∈ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a :=
          ⟨hx, hy⟩
        rw [modelProduct, indicator_of_mem hxy,
          indicator_of_mem hy]
      · have hxy :
            (x, y) ∉ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
          intro h
          exact hy h.2
        rw [modelProduct, indicator_of_notMem hxy,
          indicator_of_notMem hy]
    · have hz :
          (fun y : ℝ => modelProduct p a (x, y)) =
            (fun _ : ℝ => (0 : ℝ)) := by
        funext y
        rw [modelProduct]
        apply indicator_of_notMem
        intro h
        exact hx h.1
      rw [hz]
      exact integrable_zero ℝ ℝ volume
  have houterMeas :
      AEStronglyMeasurable
        (fun x : ℝ =>
          ∫ y : ℝ, ‖modelProduct p a (x, y)‖ ∂volume) volume :=
    hmeas.norm.integral_prod_right'
  have houterBound (x : ℝ) :
      (∫ y : ℝ, ‖modelProduct p a (x, y)‖ ∂volume) ≤
        (Icc (0 : ℝ) a).indicator (fun _ : ℝ => K) x := by
    by_cases hx : x ∈ Icc (0 : ℝ) a
    · rw [indicator_of_mem hx]
      have hleft : -R ≤ x - a := by
        dsimp [R]
        rw [abs_of_pos ha]
        linarith [hx.1]
      have hright : x ≤ R := by
        dsimp [R]
        rw [abs_of_pos ha]
        linarith [hx.2]
      have hsub :
          Icc (x - a) x ⊆ Icc (-R) R := by
        intro t ht
        exact ⟨hleft.trans ht.1, ht.2.trans hright⟩
      have hmono :
          (∫ t in Icc (x - a) x, singularKernel p t) ≤ K := by
        dsimp [K]
        exact setIntegral_mono_set hbig
          (Filter.Eventually.of_forall fun t =>
            singularKernel_nonneg p t)
          (Filter.Eventually.of_forall hsub)
      have hsection :
          (fun y : ℝ => ‖modelProduct p a (x, y)‖) =
            (Icc (0 : ℝ) a).indicator
              (fun y : ℝ => singularKernel p (x - y)) := by
        funext y
        by_cases hy : y ∈ Icc (0 : ℝ) a
        · have hxy :
              (x, y) ∈ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a :=
            ⟨hx, hy⟩
          rw [modelProduct, indicator_of_mem hxy,
            indicator_of_mem hy, Real.norm_eq_abs,
            abs_of_nonneg (singularKernel_nonneg p (x - y))]
        · have hxy :
              (x, y) ∉ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
            intro h
            exact hy h.2
          rw [modelProduct, indicator_of_notMem hxy,
            indicator_of_notMem hy, norm_zero]
      rw [hsection, integral_indicator measurableSet_Icc]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le ha.le]
      rw [intervalIntegral.integral_comp_sub_left]
      simp only [sub_zero]
      rw [intervalIntegral.integral_of_le (by linarith : x - a ≤ x)]
      rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
      exact hmono
    · rw [indicator_of_notMem hx]
      have hz :
          (fun y : ℝ => ‖modelProduct p a (x, y)‖) =
            (fun _ : ℝ => (0 : ℝ)) := by
        funext y
        rw [modelProduct]
        have hxy :
            (x, y) ∉ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
          intro h
          exact hx h.1
        rw [indicator_of_notMem hxy, norm_zero]
      rw [hz]
      simp
  have hmajorant :
      Integrable ((Icc (0 : ℝ) a).indicator (fun _ : ℝ => K))
        volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      continuous_const.integrableOn_Icc
  have houter :
      Integrable
        (fun x : ℝ =>
          ∫ y : ℝ, ‖modelProduct p a (x, y)‖ ∂volume) volume := by
    refine hmajorant.mono' houterMeas ?_
    filter_upwards with x
    have hnonneg :
        0 ≤ (∫ y : ℝ, ‖modelProduct p a (x, y)‖ ∂volume) :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun y => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact houterBound x
  exact (integrable_prod_iff hmeas).mpr ⟨hsections, houter⟩

private theorem integrand_integrable_of_lt
    (φ : Point2 → ℝ) (a p : ℝ) (ha : 0 < a)
    (hφ : ContinuousOn φ (square a))
    (hbounded : ∃ M : ℝ, ∀ q ∈ square a, |φ q| ≤ M)
    (hp : p < 1) :
    IntegrableOn (weightedKernelOnPoint φ p) (square a) volume := by
  have hsquareMeas : MeasurableSet (square a) := by
    rw [square_eq_prod]
    exact measurableSet_Icc.prod measurableSet_Icc
  rcases hbounded with ⟨M, hM⟩
  let D : ℝ := max M 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hDφ : ∀ q ∈ square a, |φ q| ≤ D := by
    intro q hq
    exact (hM q hq).trans (le_max_left _ _)
  have hmodel :
      Integrable (modelProduct p a)
        ((volume : Measure ℝ).prod volume) :=
    modelProduct_integrable a p ha hp
  have hφind :
      AEStronglyMeasurable ((square a).indicator φ)
        ((volume : Measure ℝ).prod volume) := by
    apply (aestronglyMeasurable_indicator_iff hsquareMeas).mpr
    exact hφ.aestronglyMeasurable hsquareMeas
  have hφindBound :
      ∀ᵐ q ∂((volume : Measure ℝ).prod volume),
        ‖(square a).indicator φ q‖ ≤ D := by
    filter_upwards with q
    by_cases hq : q ∈ square a
    · rw [indicator_of_mem hq, Real.norm_eq_abs]
      exact hDφ q hq
    · rw [indicator_of_notMem hq, norm_zero]
      exact hD0
  have hweighted :
      Integrable
        (fun q : Point2 =>
          (square a).indicator φ q * modelProduct p a q)
        ((volume : Measure ℝ).prod volume) :=
    hmodel.bdd_mul hφind hφindBound
  have heq :
      (square a).indicator (weightedKernelOnPoint φ p) =
        (fun q : Point2 =>
          (square a).indicator φ q * modelProduct p a q) := by
    funext q
    by_cases hq : q ∈ square a
    · have hq' :
          q ∈ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
        rw [← square_eq_prod]
        exact hq
      rw [indicator_of_mem hq, indicator_of_mem hq,
        modelProduct, indicator_of_mem hq']
      simp only [weightedKernelOnPoint, weightedKernel,
        singularKernel, div_eq_mul_inv, one_mul]
    · have hq' :
          q ∉ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
        rw [← square_eq_prod]
        exact hq
      rw [indicator_of_notMem hq, indicator_of_notMem hq,
        modelProduct, indicator_of_notMem hq', zero_mul]
  apply (integrable_indicator_iff hsquareMeas).mp
  rw [Measure.volume_eq_prod, heq]
  exact hweighted

private theorem integrand_integrable_implies_lt
    (φ : Point2 → ℝ) (a p m : ℝ) (ha : 0 < a)
    (hφ : ContinuousOn φ (square a))
    (hm0 : 0 < m)
    (hm : ∀ q ∈ square a, m ≤ |φ q|)
    (hint : IntegrableOn (weightedKernelOnPoint φ p) (square a) volume) :
    p < 1 := by
  have hsquareMeas : MeasurableSet (square a) := by
    rw [square_eq_prod]
    exact measurableSet_Icc.prod measurableSet_Icc
  have hweighted :
      Integrable ((square a).indicator (weightedKernelOnPoint φ p))
        ((volume : Measure ℝ).prod volume) := by
    have h :=
      (integrable_indicator_iff hsquareMeas).mpr hint
    rw [Measure.volume_eq_prod] at h
    exact h
  have hφne : ∀ q ∈ square a, φ q ≠ 0 := by
    intro q hq hzero
    have := hm q hq
    rw [hzero, abs_zero] at this
    linarith
  have hinvCont :
      ContinuousOn (fun q : Point2 => 1 / φ q) (square a) := by
    exact continuousOn_const.div hφ hφne
  have hinvMeas :
      AEStronglyMeasurable
        ((square a).indicator (fun q : Point2 => 1 / φ q))
        ((volume : Measure ℝ).prod volume) := by
    apply (aestronglyMeasurable_indicator_iff hsquareMeas).mpr
    exact hinvCont.aestronglyMeasurable hsquareMeas
  have hinvBound :
      ∀ᵐ q ∂((volume : Measure ℝ).prod volume),
        ‖(square a).indicator (fun q : Point2 => 1 / φ q) q‖ ≤
          1 / m := by
    filter_upwards with q
    by_cases hq : q ∈ square a
    · rw [indicator_of_mem hq, Real.norm_eq_abs, abs_div,
          abs_one]
      exact one_div_le_one_div_of_le hm0 (hm q hq)
    · rw [indicator_of_notMem hq, norm_zero]
      positivity
  have hcancelled :
      Integrable
        (fun q : Point2 =>
          (square a).indicator (fun q : Point2 => 1 / φ q) q *
            (square a).indicator (weightedKernelOnPoint φ p) q)
        ((volume : Measure ℝ).prod volume) :=
    hweighted.bdd_mul hinvMeas hinvBound
  have hmodel :
      Integrable (modelProduct p a)
        ((volume : Measure ℝ).prod volume) := by
    convert hcancelled using 1
    funext q
    by_cases hq : q ∈ square a
    · have hq' :
          q ∈ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
        rw [← square_eq_prod]
        exact hq
      rw [modelProduct, indicator_of_mem hq',
        indicator_of_mem hq, indicator_of_mem hq]
      unfold weightedKernelOnPoint weightedKernel singularKernel
      rw [← mul_div_assoc, one_div_mul_cancel (hφne q hq)]
    · have hq' :
          q ∉ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
        rw [← square_eq_prod]
        exact hq
      rw [modelProduct, indicator_of_notMem hq',
        indicator_of_notMem hq, indicator_of_notMem hq,
        zero_mul]
  have hsections :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Integrable (fun y : ℝ => modelProduct p a (x, y)) volume :=
    ((integrable_prod_iff
      (modelProduct_measurable p a).aestronglyMeasurable).mp hmodel).1
  have hIooMeasure :
      (volume : Measure ℝ) (Ioo (0 : ℝ) a) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp only [sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr ha
  have hsections' :
      ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioo (0 : ℝ) a),
        Integrable (fun y : ℝ => modelProduct p a (x, y)) volume :=
    ae_mono Measure.restrict_le_self hsections
  obtain ⟨x, hx, hxint⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      hIooMeasure hsections'
  have hxIcc : x ∈ Icc (0 : ℝ) a :=
    ⟨hx.1.le, hx.2.le⟩
  have hsectionEq :
      (fun y : ℝ => modelProduct p a (x, y)) =
        (Icc (0 : ℝ) a).indicator
          (fun y : ℝ => singularKernel p (x - y)) := by
    funext y
    by_cases hy : y ∈ Icc (0 : ℝ) a
    · have hxy :
          (x, y) ∈ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a :=
        ⟨hxIcc, hy⟩
      rw [modelProduct, indicator_of_mem hxy,
        indicator_of_mem hy]
    · have hxy :
          (x, y) ∉ Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a := by
        intro h
        exact hy h.2
      rw [modelProduct, indicator_of_notMem hxy,
        indicator_of_notMem hy]
  rw [hsectionEq] at hxint
  have hshiftOn :
      IntegrableOn (fun y : ℝ => singularKernel p (x - y))
        (Icc (0 : ℝ) a) volume :=
    (integrable_indicator_iff measurableSet_Icc).mp hxint
  have hshiftSmall :
      IntegrableOn (fun y : ℝ => singularKernel p (x - y))
        (Icc (0 : ℝ) x) volume := by
    apply hshiftOn.mono_set
    intro y hy
    exact ⟨hy.1, hy.2.trans hx.2.le⟩
  have hshiftInterval :
      IntervalIntegrable (fun y : ℝ => singularKernel p (x - y))
        volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1.le).mpr
      hshiftSmall
  have hkernelInterval :
      IntervalIntegrable (singularKernel p) volume 0 x := by
    have h := hshiftInterval.comp_sub_left x
    have heq :
        (fun t : ℝ => singularKernel p (x - (x - t))) =
          singularKernel p := by
      funext t
      congr 1
      ring
    rw [heq] at h
    simpa only [sub_zero, sub_self] using h.symm
  have hkernelOn :
      IntegrableOn (singularKernel p) (Ioo (0 : ℝ) x) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le).mp
      hkernelInterval
  have hrpowOn :
      IntegrableOn (fun t : ℝ => Real.rpow t (-p))
        (Ioo (0 : ℝ) x) volume := by
    apply hkernelOn.congr_fun
    · intro t ht
      rw [singularKernel_eq, abs_of_pos ht.1]
    · exact measurableSet_Ioo
  have hexponent :
      -1 < -p :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hx.1).mp hrpowOn
  linarith

private theorem square_measurable (a : ℝ) :
    MeasurableSet (square a) := by
  rw [square_eq_prod]
  exact measurableSet_Icc.prod measurableSet_Icc

private theorem square_compact (a : ℝ) :
    IsCompact (square a) := by
  rw [square_eq_prod]
  exact isCompact_Icc.prod isCompact_Icc

private theorem zero_mem_square (a : ℝ) (ha : 0 ≤ a) :
    (0, 0) ∈ square a := by
  simp [square, ha]

private theorem modelKernel_nonneg (p x y : ℝ) :
    0 ≤ modelKernel p x y := by
  unfold modelKernel
  exact one_div_nonneg.mpr
    (Real.rpow_nonneg (abs_nonneg (x - y)) p)

private theorem modelIntegral_nonneg
    (a p : ℝ) (ha : 0 ≤ a) :
    0 ≤ modelIntegral a p := by
  unfold modelIntegral
  apply intervalIntegral.integral_nonneg ha
  intro x hx
  apply intervalIntegral.integral_nonneg ha
  intro y hy
  exact modelKernel_nonneg p x y

private theorem exists_abs_bound_on_square
    (phi : ℝ × ℝ → ℝ) (a : ℝ)
    (hcont : ContinuousOn phi (square a)) :
    ∃ M : ℝ, ∀ z ∈ square a, |phi z| ≤ M := by
  obtain ⟨M, hM⟩ :=
    (square_compact a).bddAbove_image hcont.norm
  refine ⟨M, ?_⟩
  intro z hz
  have h := hM (Set.mem_image_of_mem (fun w => ‖phi w‖) hz)
  simpa [Real.norm_eq_abs] using h

private theorem segment_mem_square
    (a : ℝ) (z : ℝ × ℝ) (hz : z ∈ square a)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (t * z.1, t * z.2) ∈ square a := by
  rcases hz with ⟨hzx0, hzxa, hzy0, hzya⟩
  exact ⟨mul_nonneg ht.1 hzx0,
    (mul_le_of_le_one_left hzx0 ht.2).trans hzxa,
    mul_nonneg ht.1 hzy0,
    (mul_le_of_le_one_left hzy0 ht.2).trans hzya⟩

private theorem phi_uniform_sign
    (phi : ℝ × ℝ → ℝ) (a m : ℝ)
    (ha : 0 < a) (hm0 : 0 < m)
    (hcont : ContinuousOn phi (square a))
    (hm : ∀ z ∈ square a, m ≤ |phi z|) :
    (∀ z ∈ square a, m ≤ phi z) ∨
      (∀ z ∈ square a, phi z ≤ -m) := by
  have hzero_abs := hm (0, 0) (zero_mem_square a ha.le)
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
          Set.MapsTo path (Set.Icc (0 : ℝ) 1) (square a) := by
        intro t ht
        exact segment_mem_square a z hz t ht
      have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
        hcont.comp hpath.continuousOn hmaps
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
      have hzero_at_t := hm (path t) (hmaps ht)
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
          Set.MapsTo path (Set.Icc (0 : ℝ) 1) (square a) := by
        intro t ht
        exact segment_mem_square a z hz t ht
      have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
        hcont.comp hpath.continuousOn hmaps
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
      have hzero_at_t := hm (path t) (hmaps ht)
      rw [show phi (path t) = 0 by
        simpa [f] using hft, abs_zero] at hzero_at_t
      linarith
    · linarith

private theorem model_section_intervalIntegrable
    (p x c d : ℝ) (hp : p < 1) :
    IntervalIntegrable (fun y => modelKernel p x y)
      volume c d := by
  change
    IntervalIntegrable
      (fun y => singularKernel p (x - y)) volume c d
  have h :=
    (singularKernel_intervalIntegrable p (x - d) (x - c) hp)
      |>.comp_sub_left x
  simpa using h.symm

private theorem singular_zero_integral
    (p b : ℝ) (hp : p < 1) (hb : 0 ≤ b) :
    (∫ t in (0 : ℝ)..b, singularKernel p t) =
      Real.rpow b (1 - p) / (1 - p) := by
  calc
    (∫ t in (0 : ℝ)..b, singularKernel p t) =
        ∫ t in (0 : ℝ)..b, Real.rpow t (-p) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hb] at ht
      rw [singularKernel_eq, abs_of_nonneg ht.1]
    _ = (Real.rpow b ((-p) + 1) -
          Real.rpow 0 ((-p) + 1)) / ((-p) + 1) :=
      integral_rpow (Or.inl (by linarith))
    _ = Real.rpow b (1 - p) / (1 - p) := by
      have hzero :
          Real.rpow 0 ((-p) + 1) = 0 := by
        change (0 : ℝ) ^ ((-p) + 1) = 0
        exact Real.zero_rpow (by linarith)
      rw [hzero]
      have hexp : (-p) + 1 = 1 - p := by ring
      rw [hexp]
      simp only [sub_zero]

private theorem lower_section_eq
    (p x : ℝ) (hp : p < 1) (hx : 0 ≤ x) :
    (∫ y in (0 : ℝ)..x, modelKernel p x y) =
      Real.rpow x (1 - p) / (1 - p) := by
  calc
    (∫ y in (0 : ℝ)..x, modelKernel p x y) =
        ∫ y in (0 : ℝ)..x, singularKernel p (x - y) := by
      rfl
    _ = ∫ t in (0 : ℝ)..x, singularKernel p t := by
      rw [intervalIntegral.integral_comp_sub_left]
      simp
    _ = Real.rpow x (1 - p) / (1 - p) :=
      singular_zero_integral p x hp hx

private theorem upper_section_eq
    (a p x : ℝ) (hp : p < 1) (hx : x ≤ a) :
    (∫ y in x..a, modelKernel p x y) =
      Real.rpow (a - x) (1 - p) / (1 - p) := by
  calc
    (∫ y in x..a, modelKernel p x y) =
        ∫ y in x..a, singularKernel p (y - x) := by
      apply intervalIntegral.integral_congr
      intro y hy
      simp [modelKernel, singularKernel, abs_sub_comm]
    _ = ∫ t in (0 : ℝ)..a - x, singularKernel p t := by
      rw [intervalIntegral.integral_comp_sub_right]
      simp
    _ = Real.rpow (a - x) (1 - p) / (1 - p) :=
      singular_zero_integral p (a - x) hp (sub_nonneg.mpr hx)

private theorem power_section_intervalIntegrable
    (a p : ℝ) (hp : p < 1) :
    IntervalIntegrable
      (fun x : ℝ => Real.rpow x (1 - p) / (1 - p))
      volume 0 a := by
  have hbase :
      IntervalIntegrable (fun x : ℝ => Real.rpow x (1 - p))
        volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow'
      (by linarith : -1 < 1 - p)
  simpa [div_eq_mul_inv, mul_comm] using
    hbase.const_mul ((1 - p)⁻¹)

private theorem lowerTriangle_eq_power
    (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    lowerTriangleIntegral a p = powerIntegral a p := by
  unfold lowerTriangleIntegral powerIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le ha.le] at hx
  change
    (∫ y in (0 : ℝ)..x, modelKernel p x y) =
      Real.rpow x (1 - p) / (1 - p)
  exact lower_section_eq p x hp hx.1

private theorem full_section_eq
    (a p x : ℝ) (hp : p < 1)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫ y in (0 : ℝ)..a, modelKernel p x y) =
      Real.rpow x (1 - p) / (1 - p) +
        Real.rpow (a - x) (1 - p) / (1 - p) := by
  have hleft :=
    model_section_intervalIntegrable p x 0 x hp
  have hright :=
    model_section_intervalIntegrable p x x a hp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hleft hright]
  rw [lower_section_eq p x hp hx0,
    upper_section_eq a p x hp hxa]

private theorem modelIntegral_eq_two_power
    (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    modelIntegral a p = 2 * powerIntegral a p := by
  have hpower :=
    power_section_intervalIntegrable a p hp
  have hpowerRev :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.rpow (a - x) (1 - p) / (1 - p))
        volume 0 a := by
    have h := hpower.comp_sub_left a
    simpa only [sub_zero, sub_self] using h.symm
  unfold modelIntegral powerIntegral
  calc
    (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a, modelKernel p x y) =
        ∫ x in (0 : ℝ)..a,
          (Real.rpow x (1 - p) / (1 - p) +
            Real.rpow (a - x) (1 - p) / (1 - p)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le ha.le] at hx
      change
        (∫ y in (0 : ℝ)..a, modelKernel p x y) =
          Real.rpow x (1 - p) / (1 - p) +
            Real.rpow (a - x) (1 - p) / (1 - p)
      exact full_section_eq a p x hp hx.1 hx.2
    _ = (∫ x in (0 : ℝ)..a,
          Real.rpow x (1 - p) / (1 - p)) +
        ∫ x in (0 : ℝ)..a,
          Real.rpow (a - x) (1 - p) / (1 - p) := by
      rw [intervalIntegral.integral_add hpower hpowerRev]
    _ = 2 * ∫ x in (0 : ℝ)..a,
          Real.rpow x (1 - p) / (1 - p) := by
      have hchange :
          (∫ x in (0 : ℝ)..a,
              (fun t : ℝ =>
                Real.rpow t (1 - p) / (1 - p)) (a - x)) =
            ∫ t in a - a..a - 0,
              Real.rpow t (1 - p) / (1 - p) :=
        intervalIntegral.integral_comp_sub_left
          (fun t : ℝ =>
            Real.rpow t (1 - p) / (1 - p)) a
      rw [hchange]
      simp only [sub_self, sub_zero]
      ring

private theorem model_integrableOn
    (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    IntegrableOn
      (fun q : ℝ × ℝ => modelKernel p q.1 q.2)
      (square a) volume := by
  apply (integrable_indicator_iff (square_measurable a)).mp
  rw [Measure.volume_eq_prod]
  have hmodel :=
    modelProduct_integrable a p ha hp
  convert hmodel using 1
  funext q
  by_cases hq : q ∈ square a
  · have hq' :
        q ∈ Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a := by
      rwa [← square_eq_prod]
    rw [Set.indicator_of_mem hq]
    unfold modelProduct
    rw [Set.indicator_of_mem hq']
    rfl
  · have hq' :
        q ∉ Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a := by
      rwa [← square_eq_prod]
    rw [Set.indicator_of_notMem hq]
    unfold modelProduct
    rw [Set.indicator_of_notMem hq']

private theorem iteratedIntegral_eq_set
    (F : ℝ × ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hF : IntegrableOn F (square a) volume) :
    (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a, F (x, y)) =
      ∫ q in square a, F q := by
  let G : ℝ × ℝ → ℝ := (square a).indicator F
  have hGvol : Integrable G volume := by
    dsimp [G]
    exact (integrable_indicator_iff (square_measurable a)).mpr hF
  have hGprod :
      Integrable G ((volume : Measure ℝ).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hGvol
  have hsections :
      (fun x : ℝ => ∫ y : ℝ, G (x, y)) =
        (Set.Icc (0 : ℝ) a).indicator
          (fun x => ∫ y in (0 : ℝ)..a, F (x, y)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) a
    · rw [Set.indicator_of_mem hx]
      have hsection :
          (fun y : ℝ => G (x, y)) =
            (Set.Icc (0 : ℝ) a).indicator
              (fun y => F (x, y)) := by
        funext y
        by_cases hy : y ∈ Set.Icc (0 : ℝ) a
        · have hxy : (x, y) ∈ square a := by
            exact ⟨hx.1, hx.2, hy.1, hy.2⟩
          simp [G, hxy, hy]
        · have hxy : (x, y) ∉ square a := by
            intro h
            exact hy ⟨h.2.2.1, h.2.2.2⟩
          simp [G, hxy, hy]
      rw [hsection, integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le ha]
    · rw [Set.indicator_of_notMem hx]
      have hzero :
          (fun y : ℝ => G (x, y)) = fun _ => (0 : ℝ) := by
        funext y
        apply Set.indicator_of_notMem
        intro h
        exact hx ⟨h.1, h.2.1⟩
      rw [hzero]
      simp
  calc
    (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a, F (x, y)) =
        ∫ x in Set.Icc (0 : ℝ) a,
          ∫ y in (0 : ℝ)..a, F (x, y) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le ha]
    _ = ∫ x : ℝ,
          (Set.Icc (0 : ℝ) a).indicator
            (fun x => ∫ y in (0 : ℝ)..a, F (x, y)) x := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ x : ℝ, ∫ y : ℝ, G (x, y) := by
      rw [← hsections]
    _ = ∫ q : ℝ × ℝ, G q := by
      rw [Measure.volume_eq_prod]
      exact (integral_prod G hGprod).symm
    _ = ∫ q in square a, F q := by
      dsimp [G]
      rw [integral_indicator (square_measurable a)]

private theorem originalProblem
    (φ : Point2 → ℝ) (a p : ℝ) (ha : 0 < a)
    (hφ : ContinuousOn φ (square a))
    (hbounded : ∃ M : ℝ, ∀ q ∈ square a, |φ q| ≤ M) :
    (p < 1 →
      IntegrableOn (weightedKernelOnPoint φ p)
        (square a) MeasureTheory.volume) ∧
    ((∃ m > 0, ∀ q ∈ square a, m ≤ |φ q|) →
      (IntegrableOn (weightedKernelOnPoint φ p)
        (square a) MeasureTheory.volume ↔ p < 1)) := by
  constructor
  · intro hp
    exact integrand_integrable_of_lt φ a p ha hφ hbounded hp
  · rintro ⟨m, hm0, hm⟩
    constructor
    · intro hint
      exact integrand_integrable_implies_lt φ a p m ha hφ hm0 hm hint
    · intro hp
      exact integrand_integrable_of_lt φ a p ha hφ hbounded hp

theorem gap1 (phi : ℝ × ℝ → ℝ) (a m p : ℝ)
    (z : ℝ × ℝ) (hz : z ∈ square a) (hne : z.1 ≠ z.2)
    (hm : ∀ w ∈ square a, m ≤ |phi w|) :
    m / Real.rpow |z.1 - z.2| p ≤
      |phi z| / Real.rpow |z.1 - z.2| p := by
  exact div_le_div_of_nonneg_right
    (hm z hz)
    (Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) p).le

theorem gap2 (phi : ℝ × ℝ → ℝ) (a : ℝ)
    (ha : 0 < a) (hcont : ContinuousOn phi (square a)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ square a, |phi z| ≤ M := by
  obtain ⟨M, hM⟩ :=
    exists_abs_bound_on_square phi a hcont
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hM z hz).trans (le_max_left _ _)

theorem gap3 (phi : ℝ × ℝ → ℝ) (a m M p : ℝ)
    (z : ℝ × ℝ) (hz : z ∈ square a) (hne : z.1 ≠ z.2)
    (hm : ∀ w ∈ square a, m ≤ |phi w|)
    (hM : ∀ w ∈ square a, |phi w| ≤ M) :
    m / Real.rpow |z.1 - z.2| p ≤
      M / Real.rpow |z.1 - z.2| p :=
  (gap1 phi a m p z hz hne hm).trans
    (div_le_div_of_nonneg_right
      (hM z hz)
      (Real.rpow_pos_of_pos
        (abs_pos.mpr (sub_ne_zero.mpr hne)) p).le)

theorem gap4 (phi : ℝ × ℝ → ℝ) (a m p : ℝ)
    (ha : 0 < a) (hp : p < 1) (hm0 : 0 < m)
    (hcont : ContinuousOn phi (square a))
    (hm : ∀ z ∈ square a, m ≤ |phi z|) :
    m * modelIntegral a p ≤ |weightedIntegral phi a p| := by
  have hmodel :
      IntegrableOn
        (fun q : ℝ × ℝ => modelKernel p q.1 q.2)
        (square a) :=
    model_integrableOn a p ha hp
  obtain ⟨M, hM⟩ :=
    exists_abs_bound_on_square phi a hcont
  have hweighted :
      IntegrableOn (weightedKernelOnPoint phi p) (square a) :=
    integrand_integrable_of_lt phi a p ha hcont ⟨M, hM⟩ hp
  have hmodelValue :
      modelIntegral a p =
        ∫ q in square a, modelKernel p q.1 q.2 := by
    unfold modelIntegral
    exact
      iteratedIntegral_eq_set
        (fun q : ℝ × ℝ => modelKernel p q.1 q.2)
        a ha.le hmodel
  have hweightedValue :
      weightedIntegral phi a p =
        ∫ q in square a, weightedKernelOnPoint phi p q := by
    unfold weightedIntegral
    exact iteratedIntegral_eq_set
      (weightedKernelOnPoint phi p) a ha.le hweighted
  rcases phi_uniform_sign phi a m ha hm0 hcont hm with hpos | hneg
  · have hminorant :
        Integrable
          (fun q : ℝ × ℝ => m * modelKernel p q.1 q.2)
          (volume.restrict (square a)) :=
      hmodel.const_mul m
    have hpoint :
        ∀ᵐ q ∂volume.restrict (square a),
          m * modelKernel p q.1 q.2 ≤
            weightedKernelOnPoint phi p q := by
      filter_upwards [ae_restrict_mem (square_measurable a)] with q hq
      have hk0 := modelKernel_nonneg p q.1 q.2
      simp only [weightedKernelOnPoint, weightedKernel,
        modelKernel, div_eq_mul_inv]
      simpa only [one_div, one_mul] using
        mul_le_mul_of_nonneg_right (hpos q hq)
          (one_div_nonneg.mpr
            (Real.rpow_nonneg (abs_nonneg (q.1 - q.2)) p))
    have hint := integral_mono_ae hminorant hweighted hpoint
    rw [hmodelValue, hweightedValue]
    have hle :
        m * (∫ q in square a, modelKernel p q.1 q.2) ≤
          ∫ q in square a, weightedKernelOnPoint phi p q := by
      simpa only [integral_const_mul] using hint
    exact hle.trans (le_abs_self _)
  · have hmajorant :
        Integrable
          (fun q : ℝ × ℝ => (-m) * modelKernel p q.1 q.2)
          (volume.restrict (square a)) :=
      hmodel.const_mul (-m)
    have hpoint :
        ∀ᵐ q ∂volume.restrict (square a),
          weightedKernelOnPoint phi p q ≤
            (-m) * modelKernel p q.1 q.2 := by
      filter_upwards [ae_restrict_mem (square_measurable a)] with q hq
      simp only [weightedKernelOnPoint, weightedKernel,
        modelKernel, div_eq_mul_inv]
      simpa only [one_div, one_mul] using
        mul_le_mul_of_nonneg_right (hneg q hq)
          (one_div_nonneg.mpr
            (Real.rpow_nonneg (abs_nonneg (q.1 - q.2)) p))
    have hint := integral_mono_ae hweighted hmajorant hpoint
    rw [hmodelValue, hweightedValue]
    have hle :
        (∫ q in square a, weightedKernelOnPoint phi p q) ≤
          (-m) * (∫ q in square a, modelKernel p q.1 q.2) := by
      simpa only [integral_const_mul] using hint
    have hneg_le :
        m * (∫ q in square a, modelKernel p q.1 q.2) ≤
          -(∫ q in square a, weightedKernelOnPoint phi p q) := by
      linarith
    exact hneg_le.trans (neg_le_abs _)

theorem gap5 (phi : ℝ × ℝ → ℝ) (a M p : ℝ)
    (ha : 0 < a) (hp : p < 1)
    (hM : ∀ z ∈ square a, |phi z| ≤ M) :
    |weightedIntegral phi a p| ≤ M * modelIntegral a p := by
  have hpower :=
    power_section_intervalIntegrable a p hp
  have hpowerRev :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.rpow (a - x) (1 - p) / (1 - p))
        volume 0 a := by
    have h := hpower.comp_sub_left a
    simpa only [sub_zero, sub_self] using h.symm
  have hmodelSections :
      IntervalIntegrable
        (fun x : ℝ =>
          ∫ y in (0 : ℝ)..a, modelKernel p x y)
        volume 0 a := by
    apply (hpower.add hpowerRev).congr
    intro x hx
    rw [Set.uIoc_of_le ha.le] at hx
    exact (full_section_eq a p x hp hx.1.le hx.2).symm
  have hinnerBound :
      ∀ x ∈ Set.Icc (0 : ℝ) a,
        ‖∫ y in (0 : ℝ)..a,
            weightedKernel phi p x y‖ ≤
          M * ∫ y in (0 : ℝ)..a, modelKernel p x y := by
    intro x hx
    have hmajor :
        IntervalIntegrable
          (fun y : ℝ => M * modelKernel p x y)
          volume 0 a :=
      (model_section_intervalIntegrable p x 0 a hp).const_mul M
    have hpoint :
      ∀ᵐ y ∂volume,
          y ∈ Set.Ioc (0 : ℝ) a →
            ‖weightedKernel phi p x y‖ ≤
              M * modelKernel p x y := by
      filter_upwards with y
      intro hy
      have hxy : (x, y) ∈ square a :=
        ⟨hx.1, hx.2, hy.1.le, hy.2⟩
      have hden :
          0 ≤ Real.rpow |x - y| p :=
        Real.rpow_nonneg (abs_nonneg (x - y)) p
      calc
        ‖weightedKernel phi p x y‖ =
            |phi (x, y)| / Real.rpow |x - y| p := by
          rw [weightedKernel, Real.norm_eq_abs, abs_div,
            abs_of_nonneg hden]
        _ ≤ M / Real.rpow |x - y| p :=
          div_le_div_of_nonneg_right (hM (x, y) hxy) hden
        _ = M * modelKernel p x y := by
          simp [modelKernel, div_eq_mul_inv]
    have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le
        ha.le hpoint hmajor
    simpa only [intervalIntegral.integral_const_mul] using hbound
  have houterMajor :
      IntervalIntegrable
        (fun x : ℝ =>
          M * ∫ y in (0 : ℝ)..a, modelKernel p x y)
        volume 0 a :=
    hmodelSections.const_mul M
  have houterPoint :
      ∀ᵐ x ∂volume,
        x ∈ Set.Ioc (0 : ℝ) a →
          ‖∫ y in (0 : ℝ)..a,
              weightedKernel phi p x y‖ ≤
            M * ∫ y in (0 : ℝ)..a, modelKernel p x y := by
    filter_upwards with x
    intro hx
    exact hinnerBound x ⟨hx.1.le, hx.2⟩
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le
      ha.le houterPoint houterMajor
  unfold weightedIntegral modelIntegral
  simpa only [Real.norm_eq_abs,
    intervalIntegral.integral_const_mul] using hbound

theorem gap6 (phi : ℝ × ℝ → ℝ) (a m M p : ℝ)
    (ha : 0 < a) (hp : p < 1) (hm0 : 0 < m)
    (hcont : ContinuousOn phi (square a))
    (hm : ∀ z ∈ square a, m ≤ |phi z|)
    (hM : ∀ z ∈ square a, |phi z| ≤ M) :
    m * modelIntegral a p ≤ M * modelIntegral a p :=
  (gap4 phi a m p ha hp hm0 hcont hm).trans
    (gap5 phi a M p ha hp hM)

theorem gap7 (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    modelIntegral a p = 2 * lowerTriangleIntegral a p := by
  rw [modelIntegral_eq_two_power a p ha hp,
    lowerTriangle_eq_power a p ha hp]

theorem gap8 (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    lowerTriangleIntegral a p = powerIntegral a p :=
  lowerTriangle_eq_power a p ha hp

theorem gap9 (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    powerIntegral a p =
      Real.rpow a (2 - p) / ((1 - p) * (2 - p)) := by
  unfold powerIntegral
  rw [intervalIntegral.integral_div]
  have hInt :
      (∫ x in (0 : ℝ)..a, Real.rpow x (1 - p)) =
        (Real.rpow a ((1 - p) + 1) -
          Real.rpow 0 ((1 - p) + 1)) / ((1 - p) + 1) := by
    convert
      (integral_rpow (a := (0 : ℝ)) (b := a) (r := 1 - p)
        (Or.inl (by linarith : -1 < 1 - p))) using 1
  rw [hInt]
  have hzero :
      Real.rpow 0 ((1 - p) + 1) = 0 := by
    change (0 : ℝ) ^ ((1 - p) + 1) = 0
    exact Real.zero_rpow (by linarith)
  rw [hzero]
  have hexp : (1 - p) + 1 = 2 - p := by ring
  rw [hexp]
  have h1 : 1 - p ≠ 0 := by linarith
  have h2 : 2 - p ≠ 0 := by linarith
  field_simp [h1, h2]
  ring

theorem gap10 (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    lowerTriangleIntegral a p =
      Real.rpow a (2 - p) / ((1 - p) * (2 - p)) :=
  (gap8 a p ha hp).trans (gap9 a p ha hp)

theorem gap11 (a p : ℝ) (ha : 0 < a) (hp : p < 1) :
    modelIntegral a p =
      2 * Real.rpow a (2 - p) / ((1 - p) * (2 - p)) := by
  rw [modelIntegral_eq_two_power a p ha hp,
    gap9 a p ha hp]
  ring

private theorem truncated_section_one
    (x epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilonx : epsilon ≤ x) :
    (∫ y in (0 : ℝ)..x - epsilon, modelKernel 1 x y) =
      Real.log x - Real.log epsilon := by
  calc
    (∫ y in (0 : ℝ)..x - epsilon, modelKernel 1 x y) =
        ∫ y in (0 : ℝ)..x - epsilon,
          singularKernel 1 (x - y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rfl
    _ = ∫ t in epsilon..x, singularKernel 1 t := by
      rw [intervalIntegral.integral_comp_sub_left]
      ring_nf
    _ = ∫ t in epsilon..x, 1 / t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hepsilonx] at ht
      have ht0 : 0 < t := hepsilon0.trans_le ht.1
      simp [singularKernel, abs_of_pos ht0]
    _ = Real.log (x / epsilon) :=
      integral_one_div_of_pos hepsilon0
        (hepsilon0.trans_le hepsilonx)
    _ = Real.log x - Real.log epsilon := by
      rw [Real.log_div
        (ne_of_gt (hepsilon0.trans_le hepsilonx))
        (ne_of_gt hepsilon0)]

private theorem truncated_section_shift
    (p x epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilonx : epsilon ≤ x) :
    (∫ y in (0 : ℝ)..x - epsilon, modelKernel p x y) =
      ∫ t in epsilon..x, Real.rpow t (-p) := by
  calc
    (∫ y in (0 : ℝ)..x - epsilon, modelKernel p x y) =
        ∫ y in (0 : ℝ)..x - epsilon,
          singularKernel p (x - y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rfl
    _ = ∫ t in epsilon..x, singularKernel p t := by
      rw [intervalIntegral.integral_comp_sub_left]
      ring_nf
    _ = ∫ t in epsilon..x, Real.rpow t (-p) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hepsilonx] at ht
      have ht0 : 0 < t := hepsilon0.trans_le ht.1
      rw [singularKernel_eq, abs_of_pos ht0]

private theorem truncated_section_rpow
    (p x epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilonx : epsilon ≤ x) (hp1 : p ≠ 1) :
    (∫ y in (0 : ℝ)..x - epsilon, modelKernel p x y) =
      (Real.rpow x (1 - p) - Real.rpow epsilon (1 - p)) /
        (1 - p) := by
  rw [truncated_section_shift p x epsilon hepsilon0 hepsilonx]
  change
    (∫ t in epsilon..x, t ^ (-p)) =
      (x ^ (1 - p) - epsilon ^ (1 - p)) / (1 - p)
  have hzero :
      (0 : ℝ) ∉ Set.uIcc epsilon x :=
    Set.notMem_uIcc_of_lt hepsilon0
      (hepsilon0.trans_le hepsilonx)
  have hne : -p ≠ (-1 : ℝ) := by
    intro h
    apply hp1
    linarith
  rw [integral_rpow
    (Or.inr ⟨hne, hzero⟩)]
  have hexponent : -p + 1 = 1 - p := by ring
  rw [hexponent]

private theorem truncated_outer_intervalIntegrable
    (a p epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilona : epsilon ≤ a) (hp1 : p ≠ 1) :
    IntervalIntegrable
      (fun x : ℝ =>
        ∫ y in (0 : ℝ)..x - epsilon, modelKernel p x y)
      volume epsilon a := by
  have hzero :
      (0 : ℝ) ∉ Set.uIcc epsilon a :=
    Set.notMem_uIcc_of_lt hepsilon0
      (hepsilon0.trans_le hepsilona)
  have hrpow :
      IntervalIntegrable
        (fun x : ℝ => Real.rpow x (1 - p))
        volume epsilon a := by
    exact intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hexpr :
      IntervalIntegrable
        (fun x : ℝ =>
          (Real.rpow x (1 - p) -
            Real.rpow epsilon (1 - p)) / (1 - p))
        volume epsilon a :=
    (hrpow.sub intervalIntegrable_const).div_const (1 - p)
  apply hexpr.congr
  intro x hx
  rw [Set.uIoc_of_le hepsilona] at hx
  exact
    (truncated_section_rpow
      p x epsilon hepsilon0 hx.1.le hp1).symm

private theorem truncated_one_le_of_one_lt
    (a b p epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilonb : epsilon ≤ b)
    (hba : b ≤ a) (hb1 : b ≤ 1) (hp : 1 < p) :
    truncatedIntegral b 1 epsilon ≤
      truncatedIntegral a p epsilon := by
  have hepsilona : epsilon ≤ a := hepsilonb.trans hba
  have hp1 : p ≠ 1 := ne_of_gt hp
  have hone :
      IntervalIntegrable
        (fun x : ℝ =>
          ∫ y in (0 : ℝ)..x - epsilon, modelKernel 1 x y)
        volume epsilon b := by
    have hlog :
        IntervalIntegrable
          (fun x : ℝ => Real.log x - Real.log epsilon)
          volume epsilon b :=
      intervalIntegral.intervalIntegrable_log'.sub
        intervalIntegrable_const
    apply hlog.congr
    intro x hx
    rw [Set.uIoc_of_le hepsilonb] at hx
    exact
      (truncated_section_one
        x epsilon hepsilon0 hx.1.le).symm
  have hpLarge :
      IntervalIntegrable
        (fun x : ℝ =>
          ∫ y in (0 : ℝ)..x - epsilon, modelKernel p x y)
        volume epsilon a :=
    truncated_outer_intervalIntegrable
      a p epsilon hepsilon0 hepsilona hp1
  have hpSmall :
      IntervalIntegrable
        (fun x : ℝ =>
          ∫ y in (0 : ℝ)..x - epsilon, modelKernel p x y)
        volume epsilon b := by
    apply hpLarge.mono_set
    rw [Set.uIcc_of_le hepsilonb,
      Set.uIcc_of_le hepsilona]
    exact Set.Icc_subset_Icc le_rfl hba
  have hsection :
      ∀ x ∈ Set.Icc epsilon b,
        (∫ y in (0 : ℝ)..x - epsilon,
            modelKernel 1 x y) ≤
          ∫ y in (0 : ℝ)..x - epsilon,
            modelKernel p x y := by
    intro x hx
    have hepsilonx : epsilon ≤ x := hx.1
    rw [truncated_section_shift
      1 x epsilon hepsilon0 hepsilonx]
    rw [truncated_section_shift
      p x epsilon hepsilon0 hepsilonx]
    have hzero :
        (0 : ℝ) ∉ Set.uIcc epsilon x :=
      Set.notMem_uIcc_of_lt hepsilon0
        (hepsilon0.trans_le hepsilonx)
    have hiOne :
        IntervalIntegrable
          (fun t : ℝ => Real.rpow t (-1))
          volume epsilon x :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
    have hiP :
        IntervalIntegrable
          (fun t : ℝ => Real.rpow t (-p))
          volume epsilon x :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
    apply intervalIntegral.integral_mono_on
      hepsilonx hiOne hiP
    intro t ht
    have ht0 : 0 < t := hepsilon0.trans_le ht.1
    have ht1 : t ≤ 1 :=
      ht.2.trans hx.2 |>.trans hb1
    exact
      Real.rpow_le_rpow_of_exponent_ge
        ht0 ht1 (by linarith : -p ≤ (-1 : ℝ))
  have hsmallCompare :
      (∫ x in epsilon..b,
          ∫ y in (0 : ℝ)..x - epsilon,
            modelKernel 1 x y) ≤
        ∫ x in epsilon..b,
          ∫ y in (0 : ℝ)..x - epsilon,
            modelKernel p x y :=
    intervalIntegral.integral_mono_on
      hepsilonb hone hpSmall hsection
  have hpNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc epsilon a)]
        (fun x : ℝ =>
          ∫ y in (0 : ℝ)..x - epsilon,
            modelKernel p x y) := by
    filter_upwards
        [ae_restrict_mem measurableSet_Ioc] with x hx
    apply intervalIntegral.integral_nonneg
      (sub_nonneg.mpr hx.1.le)
    intro y hy
    exact modelKernel_nonneg p x y
  have henlarge :
      (∫ x in epsilon..b,
          ∫ y in (0 : ℝ)..x - epsilon,
            modelKernel p x y) ≤
        ∫ x in epsilon..a,
          ∫ y in (0 : ℝ)..x - epsilon,
            modelKernel p x y :=
    intervalIntegral.integral_mono_interval
      le_rfl hepsilonb hba hpNonneg hpLarge
  unfold truncatedIntegral
  exact hsmallCompare.trans henlarge

theorem gap12 (a epsilon : ℝ)
    (ha : 0 < a) (hepsilon0 : 0 < epsilon)
    (hepsilona : epsilon < a) :
    truncatedIntegral a 1 epsilon =
      logarithmicExpression a epsilon := by
  unfold truncatedIntegral logarithmicExpression
  calc
    (∫ x in epsilon..a,
        ∫ y in (0 : ℝ)..x - epsilon, modelKernel 1 x y) =
        ∫ x in epsilon..a,
          (Real.log x - Real.log epsilon) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hepsilona.le] at hx
      exact truncated_section_one x epsilon hepsilon0 hx.1
    _ = (∫ x in epsilon..a, Real.log x) -
          ∫ x in epsilon..a, Real.log epsilon := by
      rw [intervalIntegral.integral_sub
        intervalIntegral.intervalIntegrable_log'
        intervalIntegrable_const]
    _ = (a * Real.log a - epsilon * Real.log epsilon - a + epsilon) -
          (a - epsilon) * Real.log epsilon := by
      rw [integral_log, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    _ = a * Real.log a - a + epsilon -
          a * Real.log epsilon := by
      ring

theorem gap13 (a : ℝ) (ha : 0 < a) :
    Tendsto (logarithmicExpression a)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hlog :
      Tendsto (fun epsilon : ℝ => Real.log epsilon) F atBot := by
    simpa only [F] using Real.tendsto_log_nhdsGT_zero
  refine Filter.tendsto_atTop.2 ?_
  intro B
  filter_upwards
      [self_mem_nhdsWithin,
        (Filter.tendsto_atBot.1 hlog)
          ((a * Real.log a - a - B) / a)] with
      epsilon hepsilon0 hlogBound
  have hmul :
      a * Real.log epsilon ≤ a * Real.log a - a - B := by
    calc
      a * Real.log epsilon ≤
          a * ((a * Real.log a - a - B) / a) :=
        mul_le_mul_of_nonneg_left hlogBound ha.le
      _ = a * Real.log a - a - B := by
        field_simp [ha.ne']
  have he0 : 0 < epsilon := hepsilon0
  unfold logarithmicExpression
  linarith

theorem gap14 (a : ℝ) (ha : 0 < a) :
    Tendsto (truncatedIntegral a 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hepsilona : ∀ᶠ epsilon in F, epsilon < a := by
    exact (eventually_lt_nhds ha).filter_mono inf_le_left
  have heq :
      truncatedIntegral a 1 =ᶠ[F] logarithmicExpression a := by
    filter_upwards [self_mem_nhdsWithin, hepsilona] with
      epsilon hepsilon0 hepsilona
    exact gap12 a epsilon ha hepsilon0 hepsilona
  exact (gap13 a ha).congr' heq.symm

private theorem truncated_tendsto_of_one_lt
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    Tendsto (truncatedIntegral a p)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  let b : ℝ := min a 1
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hb0 : 0 < b := by
    dsimp [b]
    exact lt_min ha zero_lt_one
  have hba : b ≤ a := by
    dsimp [b]
    exact min_le_left _ _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    exact min_le_right _ _
  have hepsilonb : ∀ᶠ epsilon in F, epsilon < b := by
    exact (eventually_lt_nhds hb0).filter_mono inf_le_left
  have hcompare :
      truncatedIntegral b 1 ≤ᶠ[F]
        truncatedIntegral a p := by
    filter_upwards [self_mem_nhdsWithin, hepsilonb] with
      epsilon hepsilon0 hepsilonb
    exact
      truncated_one_le_of_one_lt
        a b p epsilon hepsilon0 hepsilonb.le hba hb1 hp
  apply Filter.tendsto_atTop_mono' F hcompare
  simpa only [F] using gap14 b hb0

theorem gap15 (a : ℝ) (ha : 0 < a) :
    Tendsto (truncatedIntegral a 2)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
  truncated_tendsto_of_one_lt a 2 ha (by norm_num)

theorem gap16 (a p : ℝ)
    (ha : 0 < a) (hp : 1 < p) (hp2 : p ≠ 2) :
    Tendsto (truncatedIntegral a p)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
  truncated_tendsto_of_one_lt a p ha hp

theorem gap17 (phi : ℝ × ℝ → ℝ) (a m p : ℝ)
    (ha : 0 < a) (hm0 : 0 < m)
    (hcont : ContinuousOn phi (square a))
    (hm : ∀ z ∈ square a, m ≤ |phi z|) :
    IntegrableOn
        (fun z => phi z / Real.rpow |z.1 - z.2| p)
        (square a) ↔
      p < 1 := by
  change
    IntegrableOn (weightedKernelOnPoint phi p) (square a) ↔ p < 1
  constructor
  · intro hint
    exact
      integrand_integrable_implies_lt
        phi a p m ha hcont hm0 hm hint
  · intro hp
    obtain ⟨M, hM⟩ :=
      exists_abs_bound_on_square phi a hcont
    exact
      integrand_integrable_of_lt
        phi a p ha hcont ⟨M, hM⟩ hp

end

end ProofGap.Exercise4184
