import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4183

noncomputable section

open MeasureTheory Set
open scoped Interval

def diamond : Set (ℝ × ℝ) :=
  {z | |z.1| + |z.2| ≤ 1}

def firstQuadrantDiamond : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}

def denominator (p q : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.rpow |z.1| p + Real.rpow |z.2| q

def integrand (p q : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 / denominator p q z

def cutoff (p q : ℝ) : ℝ :=
  Real.rpow 2 (p - q)

def omegaLow (p q : ℝ) : Set (ℝ × ℝ) :=
  {z | z ∈ firstQuadrantDiamond ∧
    denominator p q z ≤ cutoff p q}

def omegaHigh (p q : ℝ) : Set (ℝ × ℝ) :=
  {z | z ∈ firstQuadrantDiamond ∧
    cutoff p q < denominator p q z}

/-- The corrected third region is the same low-radius piece as `omegaLow`. -/
def omegaThree (p q : ℝ) : Set (ℝ × ℝ) :=
  omegaLow p q

def coordinateMap (p q r theta : ℝ) : ℝ × ℝ :=
  (Real.rpow r (2 / p) * Real.rpow (Real.cos theta) (2 / p),
    Real.rpow r (2 / q) * Real.rpow (Real.sin theta) (2 / q))

def jacobianFactor (p q r theta : ℝ) : ℝ :=
  4 / (p * q) *
    Real.rpow r (2 / p + 2 / q - 1) *
    Real.rpow (Real.sin theta) (2 / q - 1) *
    Real.rpow (Real.cos theta) (2 / p - 1)

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

def radialUpper (p q : ℝ) : ℝ :=
  Real.rpow (Real.sqrt 2) (-(p + q))

def radialWeight (p q r : ℝ) : ℝ :=
  Real.rpow r (2 / p + 2 / q - 3)

private theorem measurable_rpow_const (a : ℝ) :
    Measurable (fun x : ℝ => x ^ a) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private theorem integrand_measurable (p q : ℝ) :
    Measurable (integrand p q) := by
  unfold integrand denominator
  exact measurable_const.div
    (((measurable_rpow_const p).comp
        (continuous_abs.measurable.comp measurable_fst)).add
      ((measurable_rpow_const q).comp
        (continuous_abs.measurable.comp measurable_snd)))

private theorem integrand_nonneg (p q : ℝ) (z : ℝ × ℝ) :
    0 ≤ integrand p q z := by
  unfold integrand denominator
  exact one_div_nonneg.mpr
    (add_nonneg
      (Real.rpow_nonneg (abs_nonneg z.1) p)
      (Real.rpow_nonneg (abs_nonneg z.2) q))

private theorem criterion_to_x_exponent
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : 1 < 1 / p + 1 / q) :
    -1 < p / q - p := by
  have hpq : p * q < p + q := by
    have hm := mul_lt_mul_of_pos_right h (mul_pos hp hq)
    field_simp [hp.ne', hq.ne'] at hm
    nlinarith
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hq]
  nlinarith

private theorem criterion_to_y_exponent
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : 1 < 1 / p + 1 / q) :
    -1 < q / p - q := by
  simpa [add_comm] using criterion_to_x_exponent q p hq hp
    (by simpa [add_comm] using h)

private theorem x_exponent_to_criterion
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : -1 < p / q - p) :
    1 < 1 / p + 1 / q := by
  have hpq : p * q < p + q := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hq] at h
    nlinarith
  have hm :
      1 * (p * q) < (1 / p + 1 / q) * (p * q) := by
    calc
      1 * (p * q) = p * q := by ring
      _ < p + q := hpq
      _ = (1 / p + 1 / q) * (p * q) := by
        field_simp [hp.ne', hq.ne']
        <;> ring
  exact lt_of_mul_lt_mul_right (by simpa using hm) (mul_pos hp hq).le

private theorem abs_rpow_integrableOn_Icc
    (a : ℝ) (ha : -1 < a) :
    IntegrableOn (fun x : ℝ => Real.rpow |x| a)
      (Icc (-1 : ℝ) 1) volume := by
  have hpos :
      IntervalIntegrable (fun x : ℝ => Real.rpow x a)
        volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' ha
  have hposAbs :
      IntervalIntegrable (fun x : ℝ => Real.rpow |x| a)
        volume 0 1 := by
    apply hpos.congr
    intro x hx
    have hx' : x ∈ Ioc (0 : ℝ) 1 := by
      simpa [uIoc_of_le zero_le_one] using hx
    change Real.rpow x a = Real.rpow |x| a
    rw [abs_of_nonneg hx'.1.le]
  have hnegBase :
      IntervalIntegrable
        (fun x : ℝ => Real.rpow (-x) a)
        volume (-1) 0 := by
    have h :=
      (IntervalIntegrable.iff_comp_neg
        (f := fun x : ℝ => Real.rpow x a)).mp hpos
    simpa using h.symm
  have hneg :
      IntervalIntegrable (fun x : ℝ => Real.rpow |x| a)
        volume (-1) 0 := by
    apply hnegBase.congr
    intro x hx
    have hx' : x ∈ Ioc (-1 : ℝ) 0 := by
      simpa [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using hx
    change Real.rpow (-x) a = Real.rpow |x| a
    rw [abs_of_nonpos hx'.2]
  have hfull :
      IntervalIntegrable (fun x : ℝ => Real.rpow |x| a)
        volume (-1) 1 :=
    hneg.trans hposAbs
  exact
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (-1 : ℝ) ≤ 1)).mp hfull

private def positiveWedge (p q c : ℝ) : Set (ℝ × ℝ) :=
  {z |
    z.1 ∈ Ioo (0 : ℝ) c ∧
      z.2 ∈ Ioo (0 : ℝ) (Real.rpow z.1 (p / q))}

private theorem positiveWedge_measurable (p q c : ℝ) :
    MeasurableSet (positiveWedge p q c) := by
  unfold positiveWedge
  apply MeasurableSet.inter
  · exact measurableSet_Ioo.preimage measurable_fst
  · exact MeasurableSet.inter
      (measurableSet_lt measurable_const measurable_snd)
      (measurableSet_lt measurable_snd
        ((measurable_rpow_const (p / q)).comp measurable_fst))

private def positiveModel (p q c : ℝ) (z : ℝ × ℝ) : ℝ :=
  (positiveWedge p q c).indicator
    (fun z => Real.rpow z.1 (-p)) z

private theorem positiveModel_measurable (p q c : ℝ) :
    Measurable (positiveModel p q c) := by
  unfold positiveModel
  exact
    ((measurable_rpow_const (-p)).comp measurable_fst).indicator
      (positiveWedge_measurable p q c)

private theorem positiveModel_section_integral
    (p q c x : ℝ) :
    (∫ y : ℝ, ‖positiveModel p q c (x, y)‖ ∂volume) =
      (Ioo (0 : ℝ) c).indicator
        (fun x => Real.rpow x (p / q - p)) x := by
  by_cases hx : x ∈ Ioo (0 : ℝ) c
  · rw [indicator_of_mem hx]
    have hfun :
        (fun y : ℝ => ‖positiveModel p q c (x, y)‖) =
          (Ioo (0 : ℝ) (Real.rpow x (p / q))).indicator
            (fun _ : ℝ => Real.rpow x (-p)) := by
      funext y
      by_cases hy : y ∈ Ioo (0 : ℝ) (Real.rpow x (p / q))
      · have hz : (x, y) ∈ positiveWedge p q c := ⟨hx, hy⟩
        rw [positiveModel, indicator_of_mem hz,
          indicator_of_mem hy, Real.norm_eq_abs]
        change |Real.rpow x (-p)| = Real.rpow x (-p)
        exact abs_of_nonneg (Real.rpow_nonneg hx.1.le (-p))
      · have hz : (x, y) ∉ positiveWedge p q c := by
          intro hz
          exact hy hz.2
        rw [positiveModel, indicator_of_notMem hz,
          indicator_of_notMem hy, norm_zero]
    rw [hfun, integral_indicator measurableSet_Ioo,
      setIntegral_const, Measure.real, Real.volume_Ioo]
    have hcut : 0 ≤ Real.rpow x (p / q) :=
      Real.rpow_nonneg hx.1.le _
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hcut)]
    simp only [sub_zero, smul_eq_mul]
    calc
      Real.rpow x (p / q) * Real.rpow x (-p) =
          Real.rpow x (p / q + -p) :=
        (Real.rpow_add hx.1 (p / q) (-p)).symm
      _ = Real.rpow x (p / q - p) := by ring_nf
  · rw [indicator_of_notMem hx]
    have hzero :
        (fun y : ℝ => ‖positiveModel p q c (x, y)‖) =
          (fun _ : ℝ => (0 : ℝ)) := by
      funext y
      have hz : (x, y) ∉ positiveWedge p q c := by
        intro hz
        exact hx hz.1
      rw [positiveModel, indicator_of_notMem hz, norm_zero]
    rw [hzero]
    simp

private theorem positiveModel_integrable_iff
    (p q c : ℝ) (hc : 0 < c) :
    Integrable (positiveModel p q c) volume ↔
      -1 < p / q - p := by
  rw [Measure.volume_eq_prod]
  have hmeas :
      AEStronglyMeasurable (positiveModel p q c)
        ((volume : Measure ℝ).prod volume) :=
    (positiveModel_measurable p q c).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  have hsections :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Integrable (fun y : ℝ => positiveModel p q c (x, y)) volume := by
    filter_upwards with x
    by_cases hx : x ∈ Ioo (0 : ℝ) c
    · have hfun :
          (fun y : ℝ => positiveModel p q c (x, y)) =
            (Ioo (0 : ℝ) (Real.rpow x (p / q))).indicator
              (fun _ : ℝ => Real.rpow x (-p)) := by
        funext y
        by_cases hy : y ∈ Ioo (0 : ℝ) (Real.rpow x (p / q))
        · have hz : (x, y) ∈ positiveWedge p q c := ⟨hx, hy⟩
          rw [positiveModel, indicator_of_mem hz,
            indicator_of_mem hy]
        · have hz : (x, y) ∉ positiveWedge p q c := by
            intro hz
            exact hy hz.2
          rw [positiveModel, indicator_of_notMem hz,
            indicator_of_notMem hy]
      rw [hfun, integrable_indicator_iff measurableSet_Ioo]
      exact integrableOn_const (hs := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    · have hzero :
          (fun y : ℝ => positiveModel p q c (x, y)) =
            (fun _ : ℝ => (0 : ℝ)) := by
        funext y
        have hz : (x, y) ∉ positiveWedge p q c := by
          intro hz
          exact hx hz.1
        rw [positiveModel, indicator_of_notMem hz]
      rw [hzero]
      exact integrable_zero ℝ ℝ volume
  simp only [hsections, true_and]
  have houter :
      (fun x : ℝ =>
        ∫ y : ℝ, ‖positiveModel p q c (x, y)‖ ∂volume) =
        (Ioo (0 : ℝ) c).indicator
          (fun x => Real.rpow x (p / q - p)) := by
    funext x
    exact positiveModel_section_integral p q c x
  rw [houter, integrable_indicator_iff measurableSet_Ioo]
  exact intervalIntegral.integrableOn_Ioo_rpow_iff hc

private def xWedge (p q : ℝ) : Set (ℝ × ℝ) :=
  {z |
    |z.1| ≤ 1 ∧
      |z.2| ≤ Real.rpow |z.1| (p / q)}

private theorem xWedge_measurable (p q : ℝ) :
    MeasurableSet (xWedge p q) := by
  unfold xWedge
  apply MeasurableSet.inter
  · exact measurableSet_le
      (continuous_abs.measurable.comp measurable_fst) measurable_const
  · exact measurableSet_le
      (continuous_abs.measurable.comp measurable_snd)
      ((measurable_rpow_const (p / q)).comp
        (continuous_abs.measurable.comp measurable_fst))

private def xModel (p q : ℝ) (z : ℝ × ℝ) : ℝ :=
  (xWedge p q).indicator
    (fun z => Real.rpow |z.1| (-p)) z

private theorem xModel_measurable (p q : ℝ) :
    Measurable (xModel p q) := by
  unfold xModel
  exact
    ((measurable_rpow_const (-p)).comp
      (continuous_abs.measurable.comp measurable_fst)).indicator
        (xWedge_measurable p q)

private theorem xModel_nonneg (p q : ℝ) (z : ℝ × ℝ) :
    0 ≤ xModel p q z := by
  unfold xModel
  by_cases hz : z ∈ xWedge p q
  · rw [indicator_of_mem hz]
    exact Real.rpow_nonneg (abs_nonneg z.1) (-p)
  · rw [indicator_of_notMem hz]

private theorem xModel_section_integral
    (p q x : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∫ y : ℝ, ‖xModel p q (x, y)‖ ∂volume) =
      (Icc (-1 : ℝ) 1).indicator
        (fun x =>
          if x = 0 then 0
          else 2 * Real.rpow |x| (p / q - p)) x := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hx]
    have hxabs : |x| ≤ 1 := (abs_le).2 hx
    let a : ℝ := Real.rpow |x| (p / q)
    have ha : 0 ≤ a := Real.rpow_nonneg (abs_nonneg x) _
    have hfun :
        (fun y : ℝ => ‖xModel p q (x, y)‖) =
          (Icc (-a) a).indicator
            (fun _ : ℝ => Real.rpow |x| (-p)) := by
      funext y
      have hyiff : y ∈ Icc (-a) a ↔ |y| ≤ a := by
        rw [mem_Icc, abs_le]
      by_cases hy : y ∈ Icc (-a) a
      · have hz : (x, y) ∈ xWedge p q := by
          exact ⟨hxabs, hyiff.mp hy⟩
        rw [xModel, indicator_of_mem hz,
          indicator_of_mem hy, Real.norm_eq_abs]
        change |Real.rpow |x| (-p)| = Real.rpow |x| (-p)
        exact abs_of_nonneg
          (Real.rpow_nonneg (abs_nonneg x) (-p))
      · have hz : (x, y) ∉ xWedge p q := by
          intro hz
          exact hy (hyiff.mpr hz.2)
        rw [xModel, indicator_of_notMem hz,
          indicator_of_notMem hy, norm_zero]
    by_cases hx0 : x = 0
    · subst x
      rw [hfun]
      have ha0 : a = 0 := by
        dsimp [a]
        simpa only [abs_zero] using
          Real.zero_rpow (div_pos hp hq).ne'
      rw [ha0]
      simp [Real.zero_rpow (neg_ne_zero.mpr hp.ne')]
    · have hxpos : 0 < |x| := abs_pos.mpr hx0
      rw [if_neg hx0, hfun, integral_indicator measurableSet_Icc,
        setIntegral_const, Measure.real, Real.volume_Icc]
      have hlen : 0 ≤ a - -a := by linarith
      rw [ENNReal.toReal_ofReal hlen]
      simp only [smul_eq_mul]
      calc
        (a - -a) * Real.rpow |x| (-p) =
            2 * (Real.rpow |x| (p / q) *
              Real.rpow |x| (-p)) := by
                dsimp [a]
                ring
        _ = 2 * Real.rpow |x| (p / q + -p) := by
          apply congrArg (fun t : ℝ => 2 * t)
          exact (Real.rpow_add hxpos (p / q) (-p)).symm
        _ = 2 * Real.rpow |x| (p / q - p) := by ring_nf
  · rw [indicator_of_notMem hx]
    have hxabs : ¬ |x| ≤ 1 := by
      intro h
      exact hx ((abs_le).1 h)
    have hzero :
        (fun y : ℝ => ‖xModel p q (x, y)‖) =
          (fun _ : ℝ => (0 : ℝ)) := by
      funext y
      have hz : (x, y) ∉ xWedge p q := by
        intro hz
        exact hxabs hz.1
      rw [xModel, indicator_of_notMem hz, norm_zero]
    rw [hzero]
    simp

private theorem xModel_integrable_of
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : 1 < 1 / p + 1 / q) :
    Integrable (xModel p q) volume := by
  rw [Measure.volume_eq_prod]
  have hmeas :
      AEStronglyMeasurable (xModel p q)
        ((volume : Measure ℝ).prod volume) :=
    (xModel_measurable p q).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards with x
    have hxabs : 0 ≤ Real.rpow |x| (p / q) :=
      Real.rpow_nonneg (abs_nonneg x) _
    by_cases hx : |x| ≤ 1
    · let a : ℝ := Real.rpow |x| (p / q)
      have hfun :
          (fun y : ℝ => xModel p q (x, y)) =
            (Icc (-a) a).indicator
              (fun _ : ℝ => Real.rpow |x| (-p)) := by
        funext y
        have hyiff : y ∈ Icc (-a) a ↔ |y| ≤ a := by
          rw [mem_Icc, abs_le]
        by_cases hy : y ∈ Icc (-a) a
        · have hz : (x, y) ∈ xWedge p q :=
            ⟨hx, hyiff.mp hy⟩
          rw [xModel, indicator_of_mem hz, indicator_of_mem hy]
        · have hz : (x, y) ∉ xWedge p q := by
            intro hz
            exact hy (hyiff.mpr hz.2)
          rw [xModel, indicator_of_notMem hz,
            indicator_of_notMem hy]
      rw [hfun, integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (hs := by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
    · have hzero :
          (fun y : ℝ => xModel p q (x, y)) =
            (fun _ : ℝ => (0 : ℝ)) := by
        funext y
        have hz : (x, y) ∉ xWedge p q := by
          intro hz
          exact hx hz.1
        rw [xModel, indicator_of_notMem hz]
      rw [hzero]
      exact integrable_zero ℝ ℝ volume
  · have houter :
        (fun x : ℝ => ∫ y : ℝ, ‖xModel p q (x, y)‖ ∂volume) =
          (Icc (-1 : ℝ) 1).indicator
            (fun x =>
              if x = 0 then 0
              else 2 * Real.rpow |x| (p / q - p)) := by
      funext x
      exact xModel_section_integral p q x hp hq
    rw [houter]
    have hregular :
        Integrable
          ((Icc (-1 : ℝ) 1).indicator
            (fun x => 2 * Real.rpow |x| (p / q - p))) volume :=
      (integrable_indicator_iff measurableSet_Icc).mpr
        ((abs_rpow_integrableOn_Icc _
          (criterion_to_x_exponent p q hp hq h)).const_mul 2)
    apply hregular.congr
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx0
    by_cases hxI : x ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hxI, indicator_of_mem hxI, if_neg hx0]
    · rw [indicator_of_notMem hxI, indicator_of_notMem hxI]

private def yWedge (p q : ℝ) : Set (ℝ × ℝ) :=
  {z |
    |z.2| ≤ 1 ∧
      |z.1| ≤ Real.rpow |z.2| (q / p)}

private theorem yWedge_measurable (p q : ℝ) :
    MeasurableSet (yWedge p q) := by
  unfold yWedge
  apply MeasurableSet.inter
  · exact measurableSet_le
      (continuous_abs.measurable.comp measurable_snd) measurable_const
  · exact measurableSet_le
      (continuous_abs.measurable.comp measurable_fst)
      ((measurable_rpow_const (q / p)).comp
        (continuous_abs.measurable.comp measurable_snd))

private def yModel (p q : ℝ) (z : ℝ × ℝ) : ℝ :=
  (yWedge p q).indicator
    (fun z => Real.rpow |z.2| (-q)) z

private theorem yModel_eq_swapped (p q : ℝ) (z : ℝ × ℝ) :
    yModel p q z = xModel q p (z.2, z.1) := by
  have hiff :
      z ∈ yWedge p q ↔ (z.2, z.1) ∈ xWedge q p := by
    rfl
  by_cases hz : z ∈ yWedge p q
  · rw [yModel, indicator_of_mem hz, xModel,
      indicator_of_mem (hiff.mp hz)]
  · rw [yModel, indicator_of_notMem hz, xModel,
      indicator_of_notMem (fun hs => hz (hiff.mpr hs))]

private theorem yModel_measurable (p q : ℝ) :
    Measurable (yModel p q) := by
  unfold yModel
  exact
    ((measurable_rpow_const (-q)).comp
      (continuous_abs.measurable.comp measurable_snd)).indicator
        (yWedge_measurable p q)

private theorem yModel_nonneg (p q : ℝ) (z : ℝ × ℝ) :
    0 ≤ yModel p q z := by
  unfold yModel
  by_cases hz : z ∈ yWedge p q
  · rw [indicator_of_mem hz]
    exact Real.rpow_nonneg (abs_nonneg z.2) (-q)
  · rw [indicator_of_notMem hz]

private theorem yModel_integrable_of
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : 1 < 1 / p + 1 / q) :
    Integrable (yModel p q) volume := by
  rw [Measure.volume_eq_prod]
  have hmeas :
      AEStronglyMeasurable (yModel p q)
        ((volume : Measure ℝ).prod volume) :=
    (yModel_measurable p q).aestronglyMeasurable
  apply (integrable_prod_iff' hmeas).mpr
  constructor
  · filter_upwards with y
    by_cases hy : |y| ≤ 1
    · let a : ℝ := Real.rpow |y| (q / p)
      have hfun :
          (fun x : ℝ => yModel p q (x, y)) =
            (Icc (-a) a).indicator
              (fun _ : ℝ => Real.rpow |y| (-q)) := by
        funext x
        have hxiff : x ∈ Icc (-a) a ↔ |x| ≤ a := by
          rw [mem_Icc, abs_le]
        by_cases hx : x ∈ Icc (-a) a
        · have hz : (x, y) ∈ yWedge p q :=
            ⟨hy, hxiff.mp hx⟩
          rw [yModel, indicator_of_mem hz, indicator_of_mem hx]
        · have hz : (x, y) ∉ yWedge p q := by
            intro hz
            exact hx (hxiff.mpr hz.2)
          rw [yModel, indicator_of_notMem hz,
            indicator_of_notMem hx]
      rw [hfun, integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (hs := by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
    · have hzero :
          (fun x : ℝ => yModel p q (x, y)) =
            (fun _ : ℝ => (0 : ℝ)) := by
        funext x
        have hz : (x, y) ∉ yWedge p q := by
          intro hz
          exact hy hz.1
        rw [yModel, indicator_of_notMem hz]
      rw [hzero]
      exact integrable_zero ℝ ℝ volume
  · have houter :
        (fun y : ℝ => ∫ x : ℝ, ‖yModel p q (x, y)‖ ∂volume) =
          (Icc (-1 : ℝ) 1).indicator
            (fun y =>
              if y = 0 then 0
              else 2 * Real.rpow |y| (q / p - q)) := by
      funext y
      simpa only [yModel_eq_swapped] using
        xModel_section_integral q p y hq hp
    rw [houter]
    have hregular :
        Integrable
          ((Icc (-1 : ℝ) 1).indicator
            (fun y => 2 * Real.rpow |y| (q / p - q))) volume :=
      (integrable_indicator_iff measurableSet_Icc).mpr
        ((abs_rpow_integrableOn_Icc _
          (criterion_to_y_exponent p q hp hq h)).const_mul 2)
    apply hregular.congr
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with y hy0
    by_cases hyI : y ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hyI, indicator_of_mem hyI, if_neg hy0]
    · rw [indicator_of_notMem hyI, indicator_of_notMem hyI]

private def closedSquare : Set (ℝ × ℝ) :=
  Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

private theorem closedSquare_measurable :
    MeasurableSet closedSquare :=
  measurableSet_Icc.prod measurableSet_Icc

private theorem closedSquare_covers
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    {z : ℝ × ℝ} (hz : z ∈ closedSquare) :
    z ∈ xWedge p q ∨ z ∈ yWedge p q := by
  have hx : |z.1| ≤ 1 := (abs_le).2 hz.1
  have hy : |z.2| ≤ 1 := (abs_le).2 hz.2
  by_cases hxy : |z.2| ≤ Real.rpow |z.1| (p / q)
  · exact Or.inl ⟨hx, hxy⟩
  · right
    refine ⟨hy, ?_⟩
    have hlt :
        Real.rpow |z.1| (p / q) < |z.2| :=
      lt_of_not_ge hxy
    have hpow :
        Real.rpow |z.1| p < Real.rpow |z.2| q := by
      have hraise :
          Real.rpow (Real.rpow |z.1| (p / q)) q <
            Real.rpow |z.2| q :=
        (Real.rpow_lt_rpow_iff
          (Real.rpow_nonneg (abs_nonneg z.1) (p / q))
          (abs_nonneg z.2) hq).mpr hlt
      calc
        Real.rpow |z.1| p =
            Real.rpow |z.1| ((p / q) * q) := by
              congr 1
              field_simp [hq.ne']
        _ = Real.rpow (Real.rpow |z.1| (p / q)) q :=
          Real.rpow_mul (abs_nonneg z.1) _ _
        _ < Real.rpow |z.2| q := hraise
    have hroot :
        |z.1| ≤ (Real.rpow |z.2| q) ^ p⁻¹ :=
      (Real.le_rpow_inv_iff_of_pos
        (abs_nonneg z.1)
        (Real.rpow_nonneg (abs_nonneg z.2) q) hp).mpr hpow.le
    calc
      |z.1| ≤ (Real.rpow |z.2| q) ^ p⁻¹ := hroot
      _ = Real.rpow |z.2| (q / p) := by
        calc
          (Real.rpow |z.2| q) ^ p⁻¹ =
              Real.rpow |z.2| (q * p⁻¹) :=
            (Real.rpow_mul (abs_nonneg z.2) q p⁻¹).symm
          _ = Real.rpow |z.2| (q / p) := by rfl

private theorem diamond_subset_closedSquare :
    diamond ⊆ closedSquare := by
  intro z hz
  have hx : |z.1| ≤ 1 := by
    exact le_trans (le_add_of_nonneg_right (abs_nonneg z.2)) hz
  have hy : |z.2| ≤ 1 := by
    exact le_trans (le_add_of_nonneg_left (abs_nonneg z.1)) hz
  exact ⟨(abs_le).1 hx, (abs_le).1 hy⟩

private theorem integrand_integrable_on_diamond_of
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : 1 < 1 / p + 1 / q) :
    IntegrableOn (integrand p q) diamond volume := by
  let F : ℝ × ℝ → ℝ :=
    closedSquare.indicator (integrand p q)
  have hFmeas : Measurable F := by
    exact (integrand_measurable p q).indicator closedSquare_measurable
  have hmajor :
      Integrable (fun z => xModel p q z + yModel p q z) volume :=
    (xModel_integrable_of p q hp hq h).add
      (yModel_integrable_of p q hp hq h)
  have hF : Integrable F volume := by
    apply hmajor.mono' hFmeas.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ closedSquare
    · rw [show F z = integrand p q z by
          simp [F, hz],
        abs_of_nonneg (integrand_nonneg p q z)]
      rcases closedSquare_covers p q hp hq hz with hx | hy
      · have hx0 : z.1 = 0 → z.2 = 0 := by
          intro hxzero
          have hzy : |z.2| ≤ 0 := by
            have hquot : 0 < p / q := div_pos hp hq
            simpa [xWedge, hxzero, Real.zero_rpow hquot.ne'] using hx.2
          exact abs_eq_zero.mp (le_antisymm hzy (abs_nonneg z.2))
        by_cases hxzero : z.1 = 0
        · have hyzero := hx0 hxzero
          have hzzero : z = (0, 0) := Prod.ext hxzero hyzero
          rw [hzzero]
          have hzeroInt : integrand p q (0, 0) = 0 := by
            simp [integrand, denominator, Real.zero_rpow hp.ne',
              Real.zero_rpow hq.ne']
          rw [hzeroInt]
          exact add_nonneg
            (xModel_nonneg p q (0, 0))
            (yModel_nonneg p q (0, 0))
        · have hxp : 0 < Real.rpow |z.1| p :=
            Real.rpow_pos_of_pos (abs_pos.mpr hxzero) p
          have hden :
              Real.rpow |z.1| p ≤
                Real.rpow |z.1| p + Real.rpow |z.2| q :=
            le_add_of_nonneg_right
              (Real.rpow_nonneg (abs_nonneg z.2) q)
          have hbound :=
            one_div_le_one_div_of_le hxp hden
          have hbound' :
              integrand p q z ≤ Real.rpow |z.1| (-p) := by
            simpa [integrand, denominator,
              Real.rpow_neg (abs_nonneg z.1) p] using hbound
          have hy0 : 0 ≤ yModel p q z := by
            unfold yModel
            by_cases hzy : z ∈ yWedge p q
            · rw [indicator_of_mem hzy]
              exact Real.rpow_nonneg (abs_nonneg z.2) (-q)
            · rw [indicator_of_notMem hzy]
          calc
            integrand p q z ≤ Real.rpow |z.1| (-p) := hbound'
            _ = xModel p q z := by
              rw [xModel, indicator_of_mem hx]
            _ ≤ xModel p q z + yModel p q z :=
              le_add_of_nonneg_right hy0
      · by_cases hyzero : z.2 = 0
        · have hzx : |z.1| ≤ 0 := by
            have hquot : 0 < q / p := div_pos hq hp
            simpa [yWedge, hyzero, Real.zero_rpow hquot.ne'] using hy.2
          have hxzero :
              z.1 = 0 :=
            abs_eq_zero.mp (le_antisymm hzx (abs_nonneg z.1))
          have hzzero : z = (0, 0) := Prod.ext hxzero hyzero
          rw [hzzero]
          have hzeroInt : integrand p q (0, 0) = 0 := by
            simp [integrand, denominator, Real.zero_rpow hp.ne',
              Real.zero_rpow hq.ne']
          rw [hzeroInt]
          exact add_nonneg
            (xModel_nonneg p q (0, 0))
            (yModel_nonneg p q (0, 0))
        · have hyp : 0 < Real.rpow |z.2| q :=
            Real.rpow_pos_of_pos (abs_pos.mpr hyzero) q
          have hden :
              Real.rpow |z.2| q ≤
                Real.rpow |z.1| p + Real.rpow |z.2| q :=
            le_add_of_nonneg_left
              (Real.rpow_nonneg (abs_nonneg z.1) p)
          have hbound :=
            one_div_le_one_div_of_le hyp hden
          have hbound' :
              integrand p q z ≤ Real.rpow |z.2| (-q) := by
            simpa [integrand, denominator,
              Real.rpow_neg (abs_nonneg z.2) q] using hbound
          have hx0 : 0 ≤ xModel p q z := by
            unfold xModel
            by_cases hzx : z ∈ xWedge p q
            · rw [indicator_of_mem hzx]
              exact Real.rpow_nonneg (abs_nonneg z.1) (-p)
            · rw [indicator_of_notMem hzx]
          calc
            integrand p q z ≤ Real.rpow |z.2| (-q) := hbound'
            _ = yModel p q z := by
              rw [yModel, indicator_of_mem hy]
            _ ≤ xModel p q z + yModel p q z := by linarith
    · have hF0 : F z = 0 := by simp [F, hz]
      rw [hF0, abs_zero]
      exact
        add_nonneg
          (by
            unfold xModel
            by_cases hzx : z ∈ xWedge p q
            · rw [indicator_of_mem hzx]
              exact Real.rpow_nonneg (abs_nonneg z.1) (-p)
            · rw [indicator_of_notMem hzx])
          (by
            unfold yModel
            by_cases hzy : z ∈ yWedge p q
            · rw [indicator_of_mem hzy]
              exact Real.rpow_nonneg (abs_nonneg z.2) (-q)
            · rw [indicator_of_notMem hzy])
  have hsquare :
      IntegrableOn (integrand p q) closedSquare volume :=
    (integrable_indicator_iff closedSquare_measurable).mp
      (by simpa [F] using hF)
  exact hsquare.mono_set diamond_subset_closedSquare

private theorem positiveWedge_subset_diamond
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    positiveWedge p q
      (min (1 / 4 : ℝ) (Real.rpow (1 / 4 : ℝ) (q / p))) ⊆
        diamond := by
  intro z hz
  let c : ℝ :=
    min (1 / 4 : ℝ) (Real.rpow (1 / 4 : ℝ) (q / p))
  have hxc : z.1 < c := hz.1.2
  have hxquarter : z.1 < 1 / 4 :=
    hxc.trans_le (min_le_left _ _)
  have hcut :
      Real.rpow z.1 (p / q) < 1 / 4 := by
    have hxroot :
        z.1 <
          Real.rpow (1 / 4 : ℝ) (q / p) :=
      hxc.trans_le (min_le_right _ _)
    have hraise :
        Real.rpow z.1 (p / q) <
          Real.rpow (Real.rpow (1 / 4 : ℝ) (q / p))
            (p / q) :=
      (Real.rpow_lt_rpow_iff
        (le_of_lt hz.1.1)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (q / p))
        (div_pos hp hq)).mpr hxroot
    calc
      Real.rpow z.1 (p / q) <
          Real.rpow (Real.rpow (1 / 4 : ℝ) (q / p))
            (p / q) := hraise
      _ = Real.rpow (1 / 4 : ℝ) ((q / p) * (p / q)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4) _ _).symm
      _ = 1 / 4 := by
        have he : (q / p) * (p / q) = 1 := by
          field_simp [hp.ne', hq.ne']
        rw [he]
        exact Real.rpow_one (1 / 4 : ℝ)
  have hyquarter : z.2 < 1 / 4 :=
    hz.2.2.trans hcut
  have hxabs : |z.1| = z.1 := abs_of_pos hz.1.1
  have hyabs : |z.2| = z.2 := abs_of_pos hz.2.1
  change |z.1| + |z.2| ≤ 1
  rw [hxabs, hyabs]
  linarith

private theorem criterion_of_integrand_integrable
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : IntegrableOn (integrand p q) diamond volume) :
    1 < 1 / p + 1 / q := by
  let c : ℝ :=
    min (1 / 4 : ℝ) (Real.rpow (1 / 4 : ℝ) (q / p))
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hwedge :
      IntegrableOn (integrand p q) (positiveWedge p q c) volume :=
    h.mono_set (by
      dsimp [c]
      exact positiveWedge_subset_diamond p q hp hq)
  have htwice :
      IntegrableOn (fun z => 2 * integrand p q z)
        (positiveWedge p q c) volume :=
    hwedge.const_mul 2
  have hpower :
      IntegrableOn (fun z : ℝ × ℝ => Real.rpow z.1 (-p))
        (positiveWedge p q c) volume := by
    apply htwice.mono'
    · exact
        ((measurable_rpow_const (-p)).comp measurable_fst).aestronglyMeasurable
    · filter_upwards
        [ae_restrict_mem (positiveWedge_measurable p q c)] with z hz
      have hxpos : 0 < z.1 := hz.1.1
      have hypos : 0 < z.2 := hz.2.1
      have hycut :
          z.2 < Real.rpow z.1 (p / q) := hz.2.2
      have hpowers :
          Real.rpow z.2 q ≤ Real.rpow z.1 p := by
        have hraise :=
          (Real.rpow_lt_rpow_iff
            (le_of_lt hypos)
            (Real.rpow_nonneg (le_of_lt hxpos) (p / q)) hq).mpr hycut
        rw [← Real.rpow_mul (le_of_lt hxpos)] at hraise
        have he : (p / q) * q = p := by
          field_simp [hq.ne']
        rw [he] at hraise
        exact hraise.le
      have hdenpos :
          0 < Real.rpow z.1 p + Real.rpow z.2 q :=
        add_pos_of_pos_of_nonneg
          (Real.rpow_pos_of_pos hxpos p)
          (Real.rpow_nonneg hypos.le q)
      have hdenle :
          Real.rpow z.1 p + Real.rpow z.2 q ≤
            2 * Real.rpow z.1 p := by
        linarith
      have hrecip :
          1 / Real.rpow z.1 p ≤
            2 * (1 /
              (Real.rpow z.1 p + Real.rpow z.2 q)) := by
        have hd :=
          (div_le_div_iff₀
            (Real.rpow_pos_of_pos hxpos p) hdenpos).mpr
            (show
              1 * (Real.rpow z.1 p + Real.rpow z.2 q) ≤
                2 * Real.rpow z.1 p by nlinarith)
        simpa using hd
      rw [Real.norm_eq_abs]
      change |Real.rpow z.1 (-p)| ≤ 2 * integrand p q z
      calc
        |Real.rpow z.1 (-p)| = Real.rpow z.1 (-p) :=
          abs_of_nonneg (Real.rpow_nonneg hxpos.le (-p))
        _ = (Real.rpow z.1 p)⁻¹ := Real.rpow_neg hxpos.le p
        _ ≤ 2 * integrand p q z := by
          simpa [integrand, denominator, abs_of_pos hxpos,
            abs_of_pos hypos] using hrecip
  have hmodel :
      Integrable (positiveModel p q c) volume :=
    (integrable_indicator_iff (positiveWedge_measurable p q c)).mpr
      hpower
  have hexponent :=
    (positiveModel_integrable_iff p q c hc).mp hmodel
  exact x_exponent_to_criterion p q hp hq hexponent

private theorem integrand_integrable_iff
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (integrand p q) diamond volume ↔
      1 < 1 / p + 1 / q := by
  constructor
  · exact criterion_of_integrand_integrable p q hp hq
  · exact integrand_integrable_on_diamond_of p q hp hq

private theorem betaKernel_intervalIntegrable
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable
      (fun t : ℝ =>
        Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1))
      volume 0 1 := by
  have huExp : -1 < u - 1 := by linarith
  have hvExp : -1 < v - 1 := by linarith
  have huPow :
      IntervalIntegrable (fun t : ℝ => Real.rpow t (u - 1))
        volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' huExp
  have hvAway :
      ContinuousOn (fun t : ℝ => Real.rpow (1 - t) (v - 1))
        (Set.uIcc (0 : ℝ) (1 / 2 : ℝ)) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    exact
      (Real.continuousAt_rpow_const (1 - t) (v - 1)
        (Or.inl (by linarith [ht.2]))).comp
        (continuous_const.sub continuous_id).continuousAt
  have hleft :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1))
        volume 0 (1 / 2 : ℝ) :=
    huPow.mul_continuousOn hvAway
  have hvPow :
      IntervalIntegrable (fun t : ℝ => Real.rpow t (v - 1))
        volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' hvExp
  have hvRight :
      IntervalIntegrable (fun t : ℝ => Real.rpow (1 - t) (v - 1))
        volume (1 / 2 : ℝ) 1 := by
    have h := (hvPow.comp_sub_left 1).symm
    convert h using 1 <;> norm_num
  have huAway :
      ContinuousOn (fun t : ℝ => Real.rpow t (u - 1))
        (Set.uIcc (1 / 2 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    exact Real.continuousAt_rpow_const t (u - 1)
      (Or.inl (by linarith [ht.1]))
  have hright :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1))
        volume (1 / 2 : ℝ) 1 :=
    hvRight.continuousOn_mul huAway
  exact hleft.trans hright

private theorem trigBeta_kernel_eq
    (u v theta : ℝ)
    (htheta0 : 0 < theta) (htheta1 : theta < Real.pi / 2) :
    (2 * Real.sin theta * Real.cos theta) *
        (Real.rpow (Real.sin theta ^ 2) (u - 1) *
          Real.rpow (1 - Real.sin theta ^ 2) (v - 1)) =
      2 *
        (Real.rpow (Real.sin theta) (2 * u - 1) *
          Real.rpow (Real.cos theta) (2 * v - 1)) := by
  have hs : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi htheta0
      (htheta1.trans (half_lt_self Real.pi_pos))
  have hc : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htheta1⟩
  have hone :
      1 - Real.sin theta ^ 2 = Real.cos theta ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hsinPow :
      Real.rpow (Real.sin theta ^ 2) (u - 1) =
        Real.rpow (Real.sin theta) (2 * (u - 1)) := by
    exact (Real.rpow_natCast_mul hs.le 2 (u - 1)).symm
  have hcosPow :
      Real.rpow (Real.cos theta ^ 2) (v - 1) =
        Real.rpow (Real.cos theta) (2 * (v - 1)) := by
    exact (Real.rpow_natCast_mul hc.le 2 (v - 1)).symm
  have hsinCombine :
      Real.sin theta *
          Real.rpow (Real.sin theta) (2 * (u - 1)) =
        Real.rpow (Real.sin theta) (2 * u - 1) := by
    calc
      Real.sin theta *
          Real.rpow (Real.sin theta) (2 * (u - 1)) =
          Real.rpow (Real.sin theta) 1 *
            Real.rpow (Real.sin theta) (2 * (u - 1)) := by
              exact congrArg
                (fun t : ℝ =>
                  t * Real.rpow (Real.sin theta) (2 * (u - 1)))
                (Real.rpow_one (Real.sin theta)).symm
      _ = Real.rpow (Real.sin theta) (1 + 2 * (u - 1)) :=
        (Real.rpow_add hs 1 (2 * (u - 1))).symm
      _ = Real.rpow (Real.sin theta) (2 * u - 1) := by ring_nf
  have hcosCombine :
      Real.cos theta *
          Real.rpow (Real.cos theta) (2 * (v - 1)) =
        Real.rpow (Real.cos theta) (2 * v - 1) := by
    calc
      Real.cos theta *
          Real.rpow (Real.cos theta) (2 * (v - 1)) =
          Real.rpow (Real.cos theta) 1 *
            Real.rpow (Real.cos theta) (2 * (v - 1)) := by
              exact congrArg
                (fun t : ℝ =>
                  t * Real.rpow (Real.cos theta) (2 * (v - 1)))
                (Real.rpow_one (Real.cos theta)).symm
      _ = Real.rpow (Real.cos theta) (1 + 2 * (v - 1)) :=
        (Real.rpow_add hc 1 (2 * (v - 1))).symm
      _ = Real.rpow (Real.cos theta) (2 * v - 1) := by ring_nf
  rw [hsinPow, hone, hcosPow]
  calc
    (2 * Real.sin theta * Real.cos theta) *
        (Real.rpow (Real.sin theta) (2 * (u - 1)) *
          Real.rpow (Real.cos theta) (2 * (v - 1))) =
      2 *
        (Real.sin theta *
          Real.rpow (Real.sin theta) (2 * (u - 1))) *
        (Real.cos theta *
          Real.rpow (Real.cos theta) (2 * (v - 1))) := by ring
    _ = 2 *
        (Real.rpow (Real.sin theta) (2 * u - 1) *
          Real.rpow (Real.cos theta) (2 * v - 1)) := by
      rw [hsinCombine, hcosCombine]
      ring

private theorem trigBeta_integral
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (∫ theta in (0 : ℝ)..Real.pi / 2,
      Real.rpow (Real.sin theta) (2 * u - 1) *
        Real.rpow (Real.cos theta) (2 * v - 1)) =
      (1 / 2 : ℝ) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t (u - 1) *
            Real.rpow (1 - t) (v - 1) := by
  let f : ℝ → ℝ := fun theta => Real.sin theta ^ 2
  let f' : ℝ → ℝ :=
    fun theta => 2 * Real.sin theta * Real.cos theta
  let g : ℝ → ℝ :=
    fun t =>
      Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
  let h : ℝ → ℝ :=
    fun theta =>
      Real.rpow (Real.sin theta) (2 * u - 1) *
        Real.rpow (Real.cos theta) (2 * v - 1)
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have hfcont :
      ContinuousOn f (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    exact (Real.continuous_sin.pow 2).continuousOn
  have hfmono :
      MonotoneOn f (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hx' : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr hpi).trans hx.1, hx.2⟩
    have hy' : y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr hpi).trans hy.1, hy.2⟩
    have hsxy : Real.sin x ≤ Real.sin y :=
      Real.monotoneOn_sin hx' hy' hxy
    have hsx0 : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (hx.2.trans (half_le_self Real.pi_pos.le))
    have hsy0 : 0 ≤ Real.sin y :=
      Real.sin_nonneg_of_nonneg_of_le_pi hy.1
        (hy.2.trans (half_le_self Real.pi_pos.le))
    dsimp [f]
    nlinarith
  have hfimage :
      f '' Set.Icc (0 : ℝ) (Real.pi / 2) =
        Set.Icc (0 : ℝ) 1 := by
    apply Set.Subset.antisymm
    · simpa [f] using hfmono.image_Icc_subset
    · simpa [f] using intermediate_value_Icc hpi hfcont
  have hfder :
      ∀ theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        HasDerivWithinAt f (f' theta)
          (Set.Icc (0 : ℝ) (Real.pi / 2)) theta := by
    intro theta htheta
    have hd :=
      (Real.hasDerivAt_sin theta).mul
        (Real.hasDerivAt_sin theta)
    apply HasDerivAt.hasDerivWithinAt
    convert hd using 1
    · funext t
      simp [f, pow_two]
    · dsimp [f']
      ring
  have hchange :
      (∫ t in Set.Icc (0 : ℝ) 1, g t) =
        ∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          f' theta • g (f theta) := by
    have hc :=
      integral_image_eq_integral_deriv_smul_of_monotoneOn
        (f := f) (f' := f')
        measurableSet_Icc hfder hfmono g
    rw [hfimage] at hc
    exact hc
  have hkernelAE :
      (fun theta => f' theta • g (f theta)) =ᵐ[
        volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))]
        (fun theta => 2 * h theta) := by
    filter_upwards
      [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ)),
        ae_restrict_of_ae
          (Measure.ae_ne volume (Real.pi / 2))] with
        theta htheta htheta0 htheta1
    have ht0 : 0 < theta := lt_of_le_of_ne htheta.1
      (Ne.symm htheta0)
    have ht1 : theta < Real.pi / 2 :=
      lt_of_le_of_ne htheta.2 htheta1
    simpa [f, f', g, h, smul_eq_mul] using
      trigBeta_kernel_eq u v theta ht0 ht1
  have hkernelIntegral :
      (∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          f' theta • g (f theta)) =
        ∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          2 * h theta :=
    integral_congr_ae hkernelAE
  have hbetaSet :
      (∫ t in Set.Icc (0 : ℝ) 1, g t) =
        ∫ t in (0 : ℝ)..1, g t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have htrigSet :
      (∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2), h theta) =
        ∫ theta in (0 : ℝ)..Real.pi / 2, h theta := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hpi]
  have htwo :
      (∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          2 * h theta) =
        2 * ∫ theta in (0 : ℝ)..Real.pi / 2, h theta := by
    rw [MeasureTheory.integral_const_mul, htrigSet]
  have hmain :
      (∫ t in (0 : ℝ)..1, g t) =
        2 * ∫ theta in (0 : ℝ)..Real.pi / 2, h theta := by
    calc
      (∫ t in (0 : ℝ)..1, g t) =
          ∫ t in Set.Icc (0 : ℝ) 1, g t := hbetaSet.symm
      _ = ∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          f' theta • g (f theta) := hchange
      _ = ∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          2 * h theta := hkernelIntegral
      _ = 2 * ∫ theta in (0 : ℝ)..Real.pi / 2, h theta := htwo
  dsimp [g, h] at hmain ⊢
  rw [hmain]
  ring

private def flipXEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ)

private def flipYEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)

private def flipXYEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.neg ℝ) (MeasurableEquiv.neg ℝ)

@[simp] private theorem flipXEquiv_apply (z : ℝ × ℝ) :
    flipXEquiv z = (-z.1, z.2) := rfl

@[simp] private theorem flipYEquiv_apply (z : ℝ × ℝ) :
    flipYEquiv z = (z.1, -z.2) := rfl

@[simp] private theorem flipXYEquiv_apply (z : ℝ × ℝ) :
    flipXYEquiv z = (-z.1, -z.2) := rfl

private theorem flipX_measurePreserving :
    MeasurePreserving flipXEquiv
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  exact MeasurePreserving.prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))
    (MeasurePreserving.id (volume : Measure ℝ))

private theorem flipY_measurePreserving :
    MeasurePreserving flipYEquiv
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  exact MeasurePreserving.prod
    (MeasurePreserving.id (volume : Measure ℝ))
    (Measure.measurePreserving_neg (volume : Measure ℝ))

private theorem flipXY_measurePreserving :
    MeasurePreserving flipXYEquiv
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  exact MeasurePreserving.prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))
    (Measure.measurePreserving_neg (volume : Measure ℝ))

private theorem firstQuadrantDiamond_measurable :
    MeasurableSet firstQuadrantDiamond := by
  unfold firstQuadrantDiamond
  exact
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le
          (measurable_fst.add measurable_snd) measurable_const))

private theorem firstQuadrantDiamond_subset_diamond :
    firstQuadrantDiamond ⊆ diamond := by
  intro z hz
  change |z.1| + |z.2| ≤ 1
  rw [abs_of_nonneg hz.1, abs_of_nonneg hz.2.1]
  exact hz.2.2

private theorem diamond_measurable :
    MeasurableSet diamond := by
  unfold diamond
  exact measurableSet_le
    ((continuous_abs.measurable.comp measurable_fst).add
      (continuous_abs.measurable.comp measurable_snd))
    measurable_const

private def quadrantIntegrand (p q : ℝ) (z : ℝ × ℝ) : ℝ :=
  firstQuadrantDiamond.indicator (integrand p q) z

private theorem quadrant_decomposition_pointwise
    (p q : ℝ) (z : ℝ × ℝ)
    (hx0 : z.1 ≠ 0) (hy0 : z.2 ≠ 0) :
    diamond.indicator (integrand p q) z =
      (quadrantIntegrand p q z +
        quadrantIntegrand p q (flipXEquiv z)) +
      (quadrantIntegrand p q (flipYEquiv z) +
        quadrantIntegrand p q (flipXYEquiv z)) := by
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · rcases lt_or_gt_of_ne hy0 with hy | hy
    · simp only [quadrantIntegrand, flipXEquiv_apply,
        flipYEquiv_apply, flipXYEquiv_apply]
      have hmem :
          z ∈ diamond ↔
            (-z.1, -z.2) ∈ firstQuadrantDiamond := by
        simp [diamond, firstQuadrantDiamond,
          abs_of_neg hx, abs_of_neg hy, hx.le, hy.le]
      have hn0 : z ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hx]
      have hnx : (-z.1, z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hy]
      have hny : (z.1, -z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hx]
      rw [indicator_of_notMem hn0, indicator_of_notMem hnx,
        indicator_of_notMem hny, zero_add, zero_add]
      by_cases hz : z ∈ diamond
      · rw [indicator_of_mem hz, indicator_of_mem (hmem.mp hz)]
        simp [integrand, denominator]
      · rw [indicator_of_notMem hz,
          indicator_of_notMem (fun hw => hz (hmem.mpr hw))]
        simp

    · simp only [quadrantIntegrand, flipXEquiv_apply,
        flipYEquiv_apply, flipXYEquiv_apply]
      have hmem :
          z ∈ diamond ↔
            (-z.1, z.2) ∈ firstQuadrantDiamond := by
        simp [diamond, firstQuadrantDiamond,
          abs_of_neg hx, abs_of_pos hy, hx.le, hy.le]
      have hn0 : z ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hx]
      have hny : (z.1, -z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hx]
      have hnxy : (-z.1, -z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hy]
      rw [indicator_of_notMem hn0, indicator_of_notMem hny,
        indicator_of_notMem hnxy, zero_add, add_zero]
      by_cases hz : z ∈ diamond
      · rw [indicator_of_mem hz, indicator_of_mem (hmem.mp hz)]
        simp [integrand, denominator]
      · rw [indicator_of_notMem hz,
          indicator_of_notMem (fun hw => hz (hmem.mpr hw))]
        simp
  · rcases lt_or_gt_of_ne hy0 with hy | hy
    · simp only [quadrantIntegrand, flipXEquiv_apply,
        flipYEquiv_apply, flipXYEquiv_apply]
      have hmem :
          z ∈ diamond ↔
            (z.1, -z.2) ∈ firstQuadrantDiamond := by
        simp [diamond, firstQuadrantDiamond,
          abs_of_pos hx, abs_of_neg hy, hx.le, hy.le]
      have hn0 : z ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hy]
      have hnx : (-z.1, z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hx]
      have hnxy : (-z.1, -z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hx]
      rw [indicator_of_notMem hn0, indicator_of_notMem hnx,
        indicator_of_notMem hnxy, zero_add, add_zero]
      by_cases hz : z ∈ diamond
      · rw [indicator_of_mem hz, indicator_of_mem (hmem.mp hz)]
        simp [integrand, denominator]
      · rw [indicator_of_notMem hz,
          indicator_of_notMem (fun hw => hz (hmem.mpr hw))]
        simp
    · simp only [quadrantIntegrand, flipXEquiv_apply,
        flipYEquiv_apply, flipXYEquiv_apply]
      have hmem :
          z ∈ diamond ↔ z ∈ firstQuadrantDiamond := by
        simp [diamond, firstQuadrantDiamond,
          abs_of_pos hx, abs_of_pos hy, hx.le, hy.le]
      have hnx : (-z.1, z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hx]
      have hny : (z.1, -z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hy]
      have hnxy : (-z.1, -z.2) ∉ firstQuadrantDiamond := by
        simp [firstQuadrantDiamond, not_le.mpr hx]
      rw [indicator_of_notMem hnx, indicator_of_notMem hny,
        indicator_of_notMem hnxy, add_zero, add_zero]
      by_cases hz : z ∈ diamond
      · rw [indicator_of_mem hz, indicator_of_mem (hmem.mp hz)]
        simp
      · rw [indicator_of_notMem hz,
          indicator_of_notMem (fun hw => hz (hmem.mpr hw))]
        simp

private theorem off_coordinate_axes_ae :
    ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      z.1 ≠ 0 ∧ z.2 ≠ 0 := by
  rw [Measure.volume_eq_prod]
  have hmeas :
      MeasurableSet
        {z : ℝ × ℝ | z.1 ≠ 0 ∧ z.2 ≠ 0} := by
    change MeasurableSet (({0}ᶜ : Set ℝ) ×ˢ ({0}ᶜ : Set ℝ))
    exact
      (MeasurableSet.compl (measurableSet_singleton (0 : ℝ))).prod
        (MeasurableSet.compl (measurableSet_singleton (0 : ℝ)))
  apply (Measure.ae_prod_iff_ae_ae hmeas).2
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with y hy
  exact ⟨hx, hy⟩

private theorem diamond_integral_eq_four_quadrant
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hcond : 1 < 1 / p + 1 / q) :
    (∫ z in diamond, integrand p q z) =
      4 * ∫ z in firstQuadrantDiamond, integrand p q z := by
  let Q : ℝ × ℝ → ℝ := quadrantIntegrand p q
  let Qx : ℝ × ℝ → ℝ := fun z => Q (flipXEquiv z)
  let Qy : ℝ × ℝ → ℝ := fun z => Q (flipYEquiv z)
  let Qxy : ℝ × ℝ → ℝ := fun z => Q (flipXYEquiv z)
  have hdiamond :
      IntegrableOn (integrand p q) diamond volume :=
    integrand_integrable_on_diamond_of p q hp hq hcond
  have hQ :
      Integrable Q (volume : Measure (ℝ × ℝ)) := by
    apply (integrable_indicator_iff firstQuadrantDiamond_measurable).mpr
    exact hdiamond.mono_set firstQuadrantDiamond_subset_diamond
  have hQprod :
      Integrable Q ((volume : Measure ℝ).prod volume) := by
    simpa only [Measure.volume_eq_prod] using hQ
  have hQxProd :
      Integrable Qx ((volume : Measure ℝ).prod volume) := by
    have h :=
      (flipX_measurePreserving.integrable_comp_emb
        flipXEquiv.measurableEmbedding).2 hQprod
    simpa [Qx, Function.comp_def] using h
  have hQyProd :
      Integrable Qy ((volume : Measure ℝ).prod volume) := by
    have h :=
      (flipY_measurePreserving.integrable_comp_emb
        flipYEquiv.measurableEmbedding).2 hQprod
    simpa [Qy, Function.comp_def] using h
  have hQxyProd :
      Integrable Qxy ((volume : Measure ℝ).prod volume) := by
    have h :=
      (flipXY_measurePreserving.integrable_comp_emb
        flipXYEquiv.measurableEmbedding).2 hQprod
    simpa [Qxy, Function.comp_def] using h
  have hQx :
      Integrable Qx (volume : Measure (ℝ × ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hQxProd
  have hQy :
      Integrable Qy (volume : Measure (ℝ × ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hQyProd
  have hQxy :
      Integrable Qxy (volume : Measure (ℝ × ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hQxyProd
  have hQxIntegral :
      (∫ z : ℝ × ℝ, Qx z) = ∫ z : ℝ × ℝ, Q z := by
    rw [Measure.volume_eq_prod]
    simpa [Qx] using flipX_measurePreserving.integral_comp' Q
  have hQyIntegral :
      (∫ z : ℝ × ℝ, Qy z) = ∫ z : ℝ × ℝ, Q z := by
    rw [Measure.volume_eq_prod]
    simpa [Qy] using flipY_measurePreserving.integral_comp' Q
  have hQxyIntegral :
      (∫ z : ℝ × ℝ, Qxy z) = ∫ z : ℝ × ℝ, Q z := by
    rw [Measure.volume_eq_prod]
    simpa [Qxy] using flipXY_measurePreserving.integral_comp' Q
  have hdecomp :
      diamond.indicator (integrand p q) =ᵐ[
        (volume : Measure (ℝ × ℝ))]
        (fun z => (Q z + Qx z) + (Qy z + Qxy z)) := by
    filter_upwards [off_coordinate_axes_ae] with z hz
    simpa [Q, Qx, Qy, Qxy] using
      quadrant_decomposition_pointwise p q z hz.1 hz.2
  have hQset :
      (∫ z : ℝ × ℝ, Q z) =
        ∫ z in firstQuadrantDiamond, integrand p q z := by
    dsimp [Q, quadrantIntegrand]
    exact integral_indicator firstQuadrantDiamond_measurable
  calc
    (∫ z in diamond, integrand p q z) =
        ∫ z : ℝ × ℝ, diamond.indicator (integrand p q) z :=
      (integral_indicator diamond_measurable).symm
    _ = ∫ z : ℝ × ℝ, (Q z + Qx z) + (Qy z + Qxy z) :=
      integral_congr_ae hdecomp
    _ = ((∫ z : ℝ × ℝ, Q z) + ∫ z : ℝ × ℝ, Qx z) +
        ((∫ z : ℝ × ℝ, Qy z) + ∫ z : ℝ × ℝ, Qxy z) := by
      calc
        (∫ z : ℝ × ℝ, (Q z + Qx z) + (Qy z + Qxy z)) =
            (∫ z : ℝ × ℝ, Q z + Qx z) +
              ∫ z : ℝ × ℝ, Qy z + Qxy z := by
          simpa only [Pi.add_apply] using
            integral_add (hQ.add hQx) (hQy.add hQxy)
        _ = ((∫ z : ℝ × ℝ, Q z) + ∫ z : ℝ × ℝ, Qx z) +
            ((∫ z : ℝ × ℝ, Qy z) + ∫ z : ℝ × ℝ, Qxy z) := by
          rw [integral_add hQ hQx, integral_add hQy hQxy]
    _ = 4 * ∫ z : ℝ × ℝ, Q z := by
      rw [hQxIntegral, hQyIntegral, hQxyIntegral]
      ring
    _ = 4 * ∫ z in firstQuadrantDiamond, integrand p q z := by
      rw [hQset]

private theorem denominator_measurable (p q : ℝ) :
    Measurable (denominator p q) := by
  unfold denominator
  exact
    ((measurable_rpow_const p).comp
      (continuous_abs.measurable.comp measurable_fst)).add
      ((measurable_rpow_const q).comp
        (continuous_abs.measurable.comp measurable_snd))

private theorem omegaLow_measurable (p q : ℝ) :
    MeasurableSet (omegaLow p q) := by
  unfold omegaLow
  exact firstQuadrantDiamond_measurable.inter
    (measurableSet_le (denominator_measurable p q) measurable_const)

private theorem omegaHigh_measurable (p q : ℝ) :
    MeasurableSet (omegaHigh p q) := by
  unfold omegaHigh
  exact firstQuadrantDiamond_measurable.inter
    (measurableSet_lt measurable_const (denominator_measurable p q))

private theorem omegaHigh_union_omegaLow (p q : ℝ) :
    omegaHigh p q ∪ omegaLow p q = firstQuadrantDiamond := by
  ext z
  by_cases hz : z ∈ firstQuadrantDiamond
  · by_cases hd : denominator p q z ≤ cutoff p q
    · simp [omegaHigh, omegaLow, hz, hd, not_lt_of_ge hd]
    · have hd' : cutoff p q < denominator p q z := lt_of_not_ge hd
      simp [omegaHigh, omegaLow, hz, hd, hd']
  · simp [omegaHigh, omegaLow, hz]

private theorem omegaHigh_disjoint_omegaLow (p q : ℝ) :
    Disjoint (omegaHigh p q) (omegaLow p q) := by
  apply Set.disjoint_left.2
  intro z hhigh hlow
  exact (not_lt_of_ge hlow.2) hhigh.2

theorem gap1 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hcond : 1 < 1 / p + 1 / q) :
    (∫ z in diamond, integrand p q z) =
      4 * (∫ z in omegaHigh p q, integrand p q z) +
        4 * (∫ z in omegaLow p q, integrand p q z) := by
  have hquad :=
    diamond_integral_eq_four_quadrant p q hp hq hcond
  have hdiamond :
      IntegrableOn (integrand p q) diamond volume :=
    integrand_integrable_on_diamond_of p q hp hq hcond
  have hhigh :
      IntegrableOn (integrand p q) (omegaHigh p q) volume :=
    hdiamond.mono_set (fun z hz =>
      firstQuadrantDiamond_subset_diamond hz.1)
  have hlow :
      IntegrableOn (integrand p q) (omegaLow p q) volume :=
    hdiamond.mono_set (fun z hz =>
      firstQuadrantDiamond_subset_diamond hz.1)
  have hsplit :
      (∫ z in firstQuadrantDiamond, integrand p q z) =
        (∫ z in omegaHigh p q, integrand p q z) +
          ∫ z in omegaLow p q, integrand p q z := by
    rw [← omegaHigh_union_omegaLow p q]
    exact setIntegral_union
      (omegaHigh_disjoint_omegaLow p q)
      (omegaLow_measurable p q) hhigh hlow
  calc
    (∫ z in diamond, integrand p q z) =
        4 * ∫ z in firstQuadrantDiamond, integrand p q z := hquad
    _ = 4 *
        ((∫ z in omegaHigh p q, integrand p q z) +
          ∫ z in omegaLow p q, integrand p q z) := by rw [hsplit]
    _ = 4 * (∫ z in omegaHigh p q, integrand p q z) +
        4 * (∫ z in omegaLow p q, integrand p q z) := by ring

theorem gap2 (p q : ℝ) :
    omegaThree p q = omegaLow p q := by
  rfl

theorem gap3 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hcond : 1 < 1 / p + 1 / q) :
    (∫ z in diamond, integrand p q z) =
      4 * (∫ z in omegaHigh p q, integrand p q z) +
        4 * (∫ z in omegaThree p q, integrand p q z) := by
  simpa [omegaThree] using gap1 p q hp hq hcond

theorem gap4 (p q r theta : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r)
    (htheta0 : 0 < theta) (htheta1 : theta < Real.pi / 2) :
    jacobianFactor p q r theta =
      4 / (p * q) *
        Real.rpow r (2 / p + 2 / q - 1) *
        Real.rpow (Real.sin theta) (2 / q - 1) *
        Real.rpow (Real.cos theta) (2 / p - 1) := by
  rfl

theorem gap5 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∫ theta in (0 : ℝ)..Real.pi / 2,
      Real.rpow (Real.sin theta) (2 / q - 1) *
        Real.rpow (Real.cos theta) (2 / p - 1)) =
      (1 / 2 : ℝ) * betaFn (1 / q) (1 / p) := by
  have hu : 0 < 1 / q := one_div_pos.mpr hq
  have hv : 0 < 1 / p := one_div_pos.mpr hp
  have hqexp : 2 * (1 / q) - 1 = 2 / q - 1 := by ring
  have hpexp : 2 * (1 / p) - 1 = 2 / p - 1 := by ring
  rw [← hqexp, ← hpexp]
  simpa [betaFn] using trigBeta_integral (1 / q) (1 / p) hu hv

theorem gap6 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (radialWeight p q)
        (Set.Ioc (0 : ℝ) (radialUpper p q)) ↔
      1 < 1 / p + 1 / q := by
  have hupper : 0 < radialUpper p q := by
    unfold radialUpper
    exact Real.rpow_pos_of_pos
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) _
  change
    IntegrableOn
        (fun r : ℝ => Real.rpow r (2 / p + 2 / q - 3))
        (Set.Ioc (0 : ℝ) (radialUpper p q)) ↔
      1 < 1 / p + 1 / q
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hpow :
      IntegrableOn
          (fun r : ℝ => Real.rpow r (2 / p + 2 / q - 3))
          (Set.Ioo (0 : ℝ) (radialUpper p q)) ↔
        -1 < 2 / p + 2 / q - 3 := by
    simpa using
      (intervalIntegral.integrableOn_Ioo_rpow_iff
        (s := 2 / p + 2 / q - 3) hupper)
  rw [hpow]
  constructor <;> intro h
  · ring_nf at h ⊢
    linarith
  · ring_nf at h ⊢
    linarith

theorem gap7 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (integrand p q) diamond ↔
      1 < 1 / p + 1 / q := by
  exact integrand_integrable_iff p q hp hq

end

end ProofGap.Exercise4183
