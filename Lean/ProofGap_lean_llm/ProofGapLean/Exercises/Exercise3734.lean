import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3734

noncomputable section

open Filter MeasureTheory
open scoped Interval Topology

def integrand (x a : ℝ) : ℝ :=
  if x = 0 then a
  else if x = Real.pi / 2 then 0
  else Real.arctan (a * Real.tan x) / Real.tan x

def integralFunction (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / 2, integrand x a

def parameterDerivativeIntegrand (x a : ℝ) : ℝ :=
  1 / (1 + a ^ 2 * Real.tan x ^ 2)

def improperRationalIntegral (a : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    1 / ((1 + t ^ 2) * (1 + a ^ 2 * t ^ 2))

def positiveConstant : ℝ := 0
def negativeConstant : ℝ := 0

private def rawIntegrand (a x : ℝ) : ℝ :=
  Real.arctan (a * Real.tan x) / Real.tan x

private def rawIntegral (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / 2, rawIntegrand a x

private def parameterKernel (s x : ℝ) : ℝ :=
  1 / (1 + s ^ 2 * Real.tan x ^ 2)

private lemma integralFunction_eq_raw (a : ℝ) :
    integralFunction a = rawIntegral a := by
  unfold integralFunction rawIntegral
  apply intervalIntegral.integral_congr_ae
  filter_upwards
    [volume.ae_ne (Real.pi / 2 : ℝ),
      volume.ae_ne (0 : ℝ)] with x hpi hzero hx
  unfold integrand rawIntegrand
  simp [hpi, hzero]

private def parameterPrimitive (s x : ℝ) : ℝ :=
  (x - s * Real.arctan (s * Real.tan x)) / (1 - s ^ 2)

private theorem parameterPrimitive_deriv (s x : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (parameterPrimitive s) (parameterKernel s x) x := by
  have hcos : Real.cos x ≠ 0 := by
    have hleft : -(Real.pi / 2) < x :=
      lt_trans (neg_lt_zero.mpr (half_pos Real.pi_pos)) hx.1
    exact (Real.cos_pos_of_mem_Ioo ⟨hleft, hx.2⟩).ne'
  have htan := Real.hasDerivAt_tan hcos
  have hinner : HasDerivAt (fun y : ℝ => s * Real.tan y)
      (s * (1 / Real.cos x ^ 2)) x := htan.const_mul s
  have harctan :=
    (Real.hasDerivAt_arctan (s * Real.tan x)).comp x hinner
  have hnum := (hasDerivAt_id x).sub (harctan.const_mul s)
  have h := hnum.div_const (1 - s ^ 2)
  convert h using 1
  have hden : 1 - s ^ 2 ≠ 0 := by
    have hsneg : s ≠ -1 := by linarith
    exact sub_ne_zero.mpr ((sq_ne_one_iff.mpr ⟨hs1, hsneg⟩).symm)
  have hcosSq : Real.cos x ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have htrig : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq x
  unfold parameterKernel
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hden, hcosSq, hcos]
  nlinarith

private theorem parameterKernel_intervalIntegrable (s : ℝ) :
    IntervalIntegrable (parameterKernel s) volume
      0 (Real.pi / 2) := by
  have hmeas : Measurable (parameterKernel s) := by
    unfold parameterKernel
    have htan : Measurable Real.tan := by
      rw [show Real.tan = fun x : ℝ => Real.sin x / Real.cos x by
        funext x
        exact Real.tan_eq_sin_div_cos x]
      exact Real.measurable_sin.div Real.measurable_cos
    exact measurable_const.div
      (measurable_const.add
        (measurable_const.mul (htan.pow_const 2)))
  have hbound : ∀ x : ℝ, ‖parameterKernel s x‖ ≤ (1 : ℝ) := by
    intro x
    have hprod : 0 ≤ s ^ 2 * Real.tan x ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hden : 1 ≤ 1 + s ^ 2 * Real.tan x ^ 2 := by linarith
    have hdenpos : 0 < 1 + s ^ 2 * Real.tan x ^ 2 := by linarith
    rw [Real.norm_eq_abs]
    unfold parameterKernel
    rw [abs_of_pos (one_div_pos.mpr hdenpos)]
    exact (div_le_one hdenpos).2 hden
  constructor
  · apply (integrableOn_const
      (s := Set.Ioc (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ))
      (measure_Ioc_lt_top
        (μ := volume) (a := (0 : ℝ))
        (b := Real.pi / 2)).ne).mono'
    · exact hmeas.aestronglyMeasurable
    · exact Eventually.of_forall hbound
  · apply (integrableOn_const
      (s := Set.Ioc (Real.pi / 2) (0 : ℝ)) (C := (1 : ℝ))
      (measure_Ioc_lt_top
        (μ := volume) (a := Real.pi / 2)
        (b := (0 : ℝ))).ne).mono'
    · exact hmeas.aestronglyMeasurable
    · exact Eventually.of_forall hbound

private theorem parameterPrimitive_tendsto_zero (s : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1) :
    Tendsto (parameterPrimitive s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have htan : ContinuousAt Real.tan 0 :=
    (Real.hasDerivAt_tan (by norm_num)).continuousAt
  have hden : 1 - s ^ 2 ≠ 0 := by
    have hsneg : s ≠ -1 := by linarith
    exact sub_ne_zero.mpr ((sq_ne_one_iff.mpr ⟨hs1, hsneg⟩).symm)
  have hc : ContinuousAt (parameterPrimitive s) 0 := by
    unfold parameterPrimitive
    fun_prop
  have hv : parameterPrimitive s 0 = 0 := by
    simp [parameterPrimitive]
  simpa only [hv] using hc.tendsto.mono_left inf_le_left

private theorem parameterPrimitive_tendsto_right (s : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1) :
    Tendsto (parameterPrimitive s) (𝓝[<] (Real.pi / 2))
      (𝓝 (Real.pi / (2 * (1 + s)))) := by
  have htan :
      Tendsto (fun x : ℝ => s * Real.tan x)
        (𝓝[<] (Real.pi / 2)) atTop :=
    Tendsto.const_mul_atTop hs Real.tendsto_tan_pi_div_two
  have harctan :
      Tendsto (fun x : ℝ => Real.arctan (s * Real.tan x))
        (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp htan).mono_right inf_le_left
  have hx :
      Tendsto (fun x : ℝ => x) (𝓝[<] (Real.pi / 2))
        (𝓝 (Real.pi / 2)) :=
    tendsto_id.mono_left inf_le_left
  have h :=
    (hx.sub (harctan.const_mul s)).div_const (1 - s ^ 2)
  have hden : 1 - s ^ 2 ≠ 0 := by
    have hsneg : s ≠ -1 := by linarith
    exact sub_ne_zero.mpr ((sq_ne_one_iff.mpr ⟨hs1, hsneg⟩).symm)
  have hval :
      (Real.pi / 2 - s * (Real.pi / 2)) / (1 - s ^ 2) =
        Real.pi / (2 * (1 + s)) := by
    field_simp [hden]
    ring
  simpa only [parameterPrimitive, hval] using h

private theorem parameterKernel_integral_value_pos_ne_one
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2, parameterKernel s x) =
      Real.pi / (2 * (1 + s)) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (b := Real.pi / 2) (half_pos Real.pi_pos)
    (fun x hx => parameterPrimitive_deriv s x hs hs1 hx)
    (parameterKernel_intervalIntegrable s)
    (parameterPrimitive_tendsto_zero s hs hs1)
    (parameterPrimitive_tendsto_right s hs hs1)
  simpa using hi

private theorem parameterKernel_integral_value_one :
    (∫ x in (0 : ℝ)..Real.pi / 2, parameterKernel 1 x) =
      Real.pi / 4 := by
  have heq :
      (∫ x in (0 : ℝ)..Real.pi / 2, parameterKernel 1 x) =
        ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (Real.pi / 2 : ℝ)] with x hxne hx
    have hx' : x ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
      simpa [Set.uIoc_of_le (half_pos Real.pi_pos).le] using hx
    have hxlt : x < Real.pi / 2 := lt_of_le_of_ne hx'.2 hxne
    have hleft : -(Real.pi / 2) < x := by
      exact (neg_lt_zero.mpr (half_pos Real.pi_pos)).trans hx'.1
    have hcos : Real.cos x ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨hleft, hxlt⟩).ne'
    have htrig := Real.sin_sq_add_cos_sq x
    unfold parameterKernel
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    nlinarith
  rw [heq, integral_cos_sq]
  simp
  ring

private theorem parameterKernel_integral_value (s : ℝ) (hs : 0 ≤ s) :
    (∫ x in (0 : ℝ)..Real.pi / 2, parameterKernel s x) =
      Real.pi / (2 * (1 + s)) := by
  rcases hs.eq_or_lt with rfl | hspos
  · simp [parameterKernel]
  · by_cases hs1 : s = 1
    · subst s
      rw [parameterKernel_integral_value_one]
      ring
    · exact parameterKernel_integral_value_pos_ne_one s hspos hs1

private theorem rawIntegrand_eq_parameterIntegral (a x : ℝ)
    (ha : 0 ≤ a) (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    rawIntegrand a x = ∫ s in (0 : ℝ)..a, parameterKernel s x := by
  have htanpos : 0 < Real.tan x :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2
  have htanne : Real.tan x ≠ 0 := htanpos.ne'
  let P : ℝ → ℝ :=
    fun s => Real.arctan (s * Real.tan x) / Real.tan x
  have hderiv : ∀ s : ℝ, HasDerivAt P (parameterKernel s x) s := by
    intro s
    have hinner : HasDerivAt (fun t : ℝ => t * Real.tan x)
        (Real.tan x) s := by
      simpa only [id_eq, one_mul] using
        (hasDerivAt_id s).mul_const (Real.tan x)
    have h :=
      ((Real.hasDerivAt_arctan (s * Real.tan x)).comp s hinner).div_const
        (Real.tan x)
    dsimp only [P]
    convert h using 1
    unfold parameterKernel
    field_simp [htanne]
  have hcont : Continuous (fun s : ℝ => parameterKernel s x) := by
    unfold parameterKernel
    exact continuous_const.div
      (continuous_const.add
        ((continuous_id.pow 2).mul continuous_const))
      (fun s => by positivity)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (hcont.intervalIntegrable 0 a)
  unfold rawIntegrand
  dsimp only [P] at hi
  simpa using hi.symm

private theorem parameterKernel_integrableOnRectangle
    (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn
      (fun p : ℝ × ℝ => parameterKernel p.2 p.1)
      (Set.Ioc (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioc (0 : ℝ) a)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  let f : ℝ × ℝ → ℝ := fun p => parameterKernel p.2 p.1
  have htan : Measurable Real.tan := by
    rw [show Real.tan = fun x : ℝ => Real.sin x / Real.cos x by
      funext x
      exact Real.tan_eq_sin_div_cos x]
    exact Real.measurable_sin.div Real.measurable_cos
  have hmeas : Measurable f := by
    dsimp only [f, parameterKernel]
    exact measurable_const.div
      (measurable_const.add
        ((measurable_snd.pow_const 2).mul
          ((htan.comp measurable_fst).pow_const 2)))
  have hbound : ∀ p : ℝ × ℝ, ‖f p‖ ≤ (1 : ℝ) := by
    intro p
    have hprod : 0 ≤ p.2 ^ 2 * Real.tan p.1 ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hden : 1 ≤ 1 + p.2 ^ 2 * Real.tan p.1 ^ 2 := by linarith
    have hdenpos : 0 < 1 + p.2 ^ 2 * Real.tan p.1 ^ 2 := by linarith
    rw [Real.norm_eq_abs]
    dsimp only [f, parameterKernel]
    rw [abs_of_pos (one_div_pos.mpr hdenpos)]
    exact (div_le_one hdenpos).2 hden
  have hxint : IntegrableOn
      (fun _x : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) (Real.pi / 2)) :=
    integrableOn_const
      (measure_Ioc_lt_top
        (μ := volume) (a := (0 : ℝ))
        (b := Real.pi / 2)).ne
  have hsint : IntegrableOn
      (fun _s : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) a) :=
    integrableOn_const
      (measure_Ioc_lt_top
        (μ := volume) (a := (0 : ℝ)) (b := a)).ne
  have hone : IntegrableOn
      (fun _p : ℝ × ℝ => (1 : ℝ))
      (Set.Ioc (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioc (0 : ℝ) a)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    unfold IntegrableOn at hxint hsint ⊢
    rw [← Measure.prod_restrict]
    simpa using hxint.mul_prod hsint
  apply hone.mono'
  · exact hmeas.aestronglyMeasurable
  · exact Eventually.of_forall hbound

private theorem parameterKernel_fubini (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        ∫ s in (0 : ℝ)..a, parameterKernel s x) =
      ∫ s in (0 : ℝ)..a,
        ∫ x in (0 : ℝ)..Real.pi / 2, parameterKernel s x := by
  let f : ℝ → ℝ → ℝ := fun x s => parameterKernel s x
  have hrect := parameterKernel_integrableOnRectangle a ha
  have hint :
      Integrable (Function.uncurry f)
        ((volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))).prod
          (volume.restrict (Set.Ioc (0 : ℝ) a))) := by
    unfold IntegrableOn at hrect
    rw [Measure.prod_restrict]
    simpa [f, Set.uIoc_of_le (half_pos Real.pi_pos).le] using hrect
  have hswap :=
    intervalIntegral_integral_swap
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (μ := volume.restrict (Set.Ioc (0 : ℝ) a)) hint
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2,
        ∫ s in (0 : ℝ)..a, parameterKernel s x) =
        ∫ x in (0 : ℝ)..Real.pi / 2,
          ∫ s : ℝ, f x s ∂(volume.restrict (Set.Ioc (0 : ℝ) a)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact intervalIntegral.integral_of_le ha
    _ = ∫ s : ℝ,
          (∫ x in (0 : ℝ)..Real.pi / 2, f x s)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) a)) := hswap
    _ = ∫ s in (0 : ℝ)..a,
          ∫ x in (0 : ℝ)..Real.pi / 2, parameterKernel s x := by
      exact (intervalIntegral.integral_of_le ha).symm

private theorem rationalParameterIntegral (a : ℝ) (ha : 0 ≤ a) :
    (∫ s in (0 : ℝ)..a, Real.pi / (2 * (1 + s))) =
      Real.pi / 2 * Real.log (1 + a) := by
  let P : ℝ → ℝ := fun s => Real.pi / 2 * Real.log (1 + s)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt P (Real.pi / (2 * (1 + s))) s := by
    intro s hs
    rw [Set.uIcc_of_le ha] at hs
    have hspos : 0 < 1 + s := by linarith [hs.1]
    have hne : 1 + s ≠ 0 := hspos.ne'
    have hlog :=
      (Real.hasDerivAt_log hne).comp s ((hasDerivAt_id s).const_add 1)
    have h := hlog.const_mul (Real.pi / 2)
    dsimp only [P]
    convert h using 1
    field_simp
  have hint : IntervalIntegrable (fun s : ℝ =>
      Real.pi / (2 * (1 + s))) volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le ha] at hs
    have hspos : 0 < 1 + s := by linarith [hs.1]
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div
        (continuousAt_const.mul (continuousAt_const.add continuousAt_id))
        (by positivity))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp only [P] at hi
  simpa using hi

private theorem positive_rawIntegral (a : ℝ) (ha : 0 < a) :
    rawIntegral a = Real.pi / 2 * Real.log (1 + a) := by
  have ha0 : 0 ≤ a := ha.le
  have horig :
      rawIntegral a =
        ∫ x in (0 : ℝ)..Real.pi / 2,
          ∫ s in (0 : ℝ)..a, parameterKernel s x := by
    unfold rawIntegral
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (Real.pi / 2 : ℝ)] with x hxne hx
    have hx' : x ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
      simpa [Set.uIoc_of_le (half_pos Real.pi_pos).le] using hx
    exact rawIntegrand_eq_parameterIntegral a x ha0
      ⟨hx'.1, lt_of_le_of_ne hx'.2 hxne⟩
  calc
    rawIntegral a =
        ∫ x in (0 : ℝ)..Real.pi / 2,
          ∫ s in (0 : ℝ)..a, parameterKernel s x := horig
    _ = ∫ s in (0 : ℝ)..a,
          ∫ x in (0 : ℝ)..Real.pi / 2, parameterKernel s x :=
      parameterKernel_fubini a ha0
    _ = ∫ s in (0 : ℝ)..a, Real.pi / (2 * (1 + s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ha0] at hs
      exact parameterKernel_integral_value s hs.1
    _ = Real.pi / 2 * Real.log (1 + a) :=
      rationalParameterIntegral a ha0

private theorem rawIntegral_neg (a : ℝ) :
    rawIntegral (-a) = -rawIntegral a := by
  unfold rawIntegral
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _
  unfold rawIntegrand
  rw [show -a * Real.tan x = -(a * Real.tan x) by ring,
    Real.arctan_neg]
  ring

private theorem rawIntegral_formula (a : ℝ) :
    rawIntegral a =
      Real.pi / 2 * Real.sign a * Real.log (1 + |a|) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hpos : 0 < -a := neg_pos.mpr ha
    have hp := positive_rawIntegral (-a) hpos
    rw [rawIntegral_neg] at hp
    rw [Real.sign_of_neg ha, abs_of_neg ha]
    norm_num at hp ⊢
    linarith
  · simp [rawIntegral, rawIntegrand]
  · rw [positive_rawIntegral a ha, Real.sign_of_pos ha, abs_of_pos ha]
    norm_num

private theorem integralFunction_formula (a : ℝ) :
    integralFunction a =
      Real.pi / 2 * Real.sign a * Real.log (1 + |a|) := by
  rw [integralFunction_eq_raw, rawIntegral_formula]

private theorem rawIntegrand_tendsto_zero (a : ℝ) :
    Tendsto (rawIntegrand a) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  by_cases ha : a = 0
  · subst a
    change Tendsto
      (fun x : ℝ => Real.arctan (0 * Real.tan x) / Real.tan x)
      (𝓝[>] (0 : ℝ)) (𝓝 0)
    simpa only [zero_mul, Real.arctan_zero, zero_div] using
      (tendsto_const_nhds :
        Tendsto (fun _x : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))
  · have htanAt : Tendsto Real.tan (𝓝 (0 : ℝ)) (𝓝 0) :=
      by
        have ht :=
          (Real.hasDerivAt_tan
            (by norm_num : Real.cos (0 : ℝ) ≠ 0)).continuousAt.tendsto
        simpa using ht
    have htan0 : Tendsto Real.tan (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      htanAt.mono_left inf_le_left
    have hinner_nhds :
        Tendsto (fun x : ℝ => a * Real.tan x)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul htan0)
    have hinner_ne :
        ∀ᶠ x in 𝓝[>] (0 : ℝ), a * Real.tan x ≠ 0 := by
      have hxlt_ev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < Real.pi / 2 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Iio_mem_nhds (half_pos Real.pi_pos))
      filter_upwards [self_mem_nhdsWithin, hxlt_ev] with x hxpos hxlt
      exact mul_ne_zero ha
        (ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hxpos hxlt))
    have hinner :
        Tendsto (fun x : ℝ => a * Real.tan x)
          (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hinner_nhds, hinner_ne⟩
    have hslope :=
      (Real.hasDerivAt_arctan 0).tendsto_slope_zero.comp hinner
    have hlim :
        Tendsto
          (fun x : ℝ =>
            a * ((a * Real.tan x)⁻¹ *
              (Real.arctan (0 + a * Real.tan x) - Real.arctan 0)))
          (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      simpa using (tendsto_const_nhds.mul hslope)
    apply hlim.congr'
    filter_upwards [hinner_ne] with x hx
    unfold rawIntegrand
    simp only [zero_add, Real.arctan_zero, sub_zero]
    field_simp

theorem gap1 (a : ℝ) :
    Tendsto (fun x => integrand x a) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  apply (rawIntegrand_tendsto_zero a).congr'
  have hxlt_ev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < Real.pi / 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (half_pos Real.pi_pos))
  filter_upwards [self_mem_nhdsWithin, hxlt_ev] with x hxpos hxlt
  have hxpos' : 0 < x := hxpos
  simp [integrand, rawIntegrand, ne_of_gt hxpos', ne_of_lt hxlt]

private theorem rawIntegrand_tendsto_pi_div_two (a : ℝ) :
    Tendsto (rawIntegrand a) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hinner :
        Tendsto (fun x : ℝ => a * Real.tan x)
          (𝓝[<] (Real.pi / 2)) atBot :=
      Tendsto.const_mul_atTop_of_neg ha Real.tendsto_tan_pi_div_two
    have hnum :
        Tendsto (fun x : ℝ => Real.arctan (a * Real.tan x))
          (𝓝[<] (Real.pi / 2)) (𝓝 (-(Real.pi / 2))) :=
      (Real.tendsto_arctan_atBot.comp hinner).mono_right inf_le_left
    simpa only [rawIntegrand] using
      hnum.div_atTop Real.tendsto_tan_pi_div_two
  · change Tendsto
      (fun x : ℝ => Real.arctan (0 * Real.tan x) / Real.tan x)
      (𝓝[<] (Real.pi / 2)) (𝓝 0)
    simpa only [zero_mul, Real.arctan_zero, zero_div] using
      (tendsto_const_nhds :
        Tendsto (fun _x : ℝ => (0 : ℝ))
          (𝓝[<] (Real.pi / 2)) (𝓝 0))
  · have hinner :
        Tendsto (fun x : ℝ => a * Real.tan x)
          (𝓝[<] (Real.pi / 2)) atTop :=
      Tendsto.const_mul_atTop ha Real.tendsto_tan_pi_div_two
    have hnum :
        Tendsto (fun x : ℝ => Real.arctan (a * Real.tan x))
          (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.comp hinner).mono_right inf_le_left
    simpa only [rawIntegrand] using
      hnum.div_atTop Real.tendsto_tan_pi_div_two

theorem gap2 (a : ℝ) :
    Tendsto (fun x => integrand x a)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  apply (rawIntegrand_tendsto_pi_div_two a).congr'
  have hxpos_ev :
      ∀ᶠ x in 𝓝[<] (Real.pi / 2), 0 < x :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioi_mem_nhds (half_pos Real.pi_pos))
  filter_upwards [self_mem_nhdsWithin, hxpos_ev] with x hxlt hxpos
  have hxlt' : x < Real.pi / 2 := hxlt
  simp [integrand, rawIntegrand, ne_of_gt hxpos, ne_of_lt hxlt']

theorem gap3 (a : ℝ) :
    ContinuousOn (fun x => integrand x a)
      (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hxpos
  · have hright :
        ContinuousWithinAt (fun x => integrand x a)
          (Set.Ioi (0 : ℝ)) 0 := by
      change Tendsto (fun x => integrand x a) (𝓝[>] (0 : ℝ))
        (𝓝 (integrand 0 a))
      have hv : integrand 0 a = a := by simp [integrand]
      rw [hv]
      exact gap1 a
    exact (continuousWithinAt_Ioi_iff_Ici.mp hright).mono
      (fun _ hy => hy.1)
  · rcases eq_or_lt_of_le hx.2 with hxeq | hxlt
    · subst x
      have hleft :
          ContinuousWithinAt (fun x => integrand x a)
            (Set.Iio (Real.pi / 2)) (Real.pi / 2) := by
        change Tendsto (fun x => integrand x a)
          (𝓝[<] (Real.pi / 2)) (𝓝 (integrand (Real.pi / 2) a))
        have hv : integrand (Real.pi / 2) a = 0 := by
          simp [integrand, ne_of_gt (half_pos Real.pi_pos)]
        rw [hv]
        exact gap2 a
      exact (continuousWithinAt_Iio_iff_Iic.mp hleft).mono
        (fun _ hy => hy.2)
    · have hleft : -(Real.pi / 2) < x := by
        linarith [half_pos Real.pi_pos]
      have hcos : Real.cos x ≠ 0 :=
        (Real.cos_pos_of_mem_Ioo ⟨hleft, hxlt⟩).ne'
      have htan : ContinuousAt Real.tan x :=
        (Real.hasDerivAt_tan hcos).continuousAt
      have htanne : Real.tan x ≠ 0 :=
        (Real.tan_pos_of_pos_of_lt_pi_div_two hxpos hxlt).ne'
      have hraw : ContinuousAt (rawIntegrand a) x := by
        unfold rawIntegrand
        exact
          (Real.continuous_arctan.continuousAt.comp
            (continuousAt_const.mul htan)).div htan htanne
      have heq :
          (fun y : ℝ => integrand y a) =ᶠ[𝓝 x] rawIntegrand a := by
        filter_upwards
          [eventually_ne_nhds (ne_of_gt hxpos),
            eventually_ne_nhds (ne_of_lt hxlt)] with y hy0 hyp
        simp [integrand, rawIntegrand, hy0, hyp]
      exact (hraw.congr_of_eventuallyEq heq).continuousWithinAt

theorem gap4 (x a : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (fun s => integrand x s) a =
      parameterDerivativeIntegrand x a := by
  have htanpos : 0 < Real.tan x :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2
  have htanne : Real.tan x ≠ 0 := htanpos.ne'
  have hinner :
      HasDerivAt (fun s : ℝ => s * Real.tan x) (Real.tan x) a := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id a).mul_const (Real.tan x)
  have hraw :
      HasDerivAt
        (fun s : ℝ => Real.arctan (s * Real.tan x) / Real.tan x)
        (1 / (1 + a ^ 2 * Real.tan x ^ 2)) a := by
    have h :=
      ((Real.hasDerivAt_arctan (a * Real.tan x)).comp a hinner).div_const
        (Real.tan x)
    convert h using 1
    field_simp [htanne]
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hxpi : x ≠ Real.pi / 2 := ne_of_lt hx.2
  simpa [integrand, parameterDerivativeIntegrand, hx0, hxpi] using hraw.deriv

theorem gap5 (a : ℝ) :
    deriv (fun s => integrand 0 s) a = 1 := by
  simp [integrand]

theorem gap6 (a : ℝ) :
    deriv (fun s => integrand (Real.pi / 2) s) a = 0 := by
  simp [integrand, ne_of_gt (half_pos Real.pi_pos)]

private theorem measurable_integrand (a : ℝ) :
    Measurable (fun x : ℝ => integrand x a) := by
  have htan : Measurable Real.tan := by
    rw [show Real.tan = fun x : ℝ => Real.sin x / Real.cos x by
      funext x
      exact Real.tan_eq_sin_div_cos x]
    exact Real.measurable_sin.div Real.measurable_cos
  have hraw :
      Measurable
        (fun x : ℝ =>
          Real.arctan (a * Real.tan x) / Real.tan x) :=
    (Real.continuous_arctan.measurable.comp
      (measurable_const.mul htan)).div htan
  unfold integrand
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Measurable.ite (measurableSet_singleton (Real.pi / 2))
      measurable_const hraw)

private theorem measurable_parameterDerivativeIntegrand (a : ℝ) :
    Measurable (fun x : ℝ => parameterDerivativeIntegrand x a) := by
  have htan : Measurable Real.tan := by
    rw [show Real.tan = fun x : ℝ => Real.sin x / Real.cos x by
      funext x
      exact Real.tan_eq_sin_div_cos x]
    exact Real.measurable_sin.div Real.measurable_cos
  unfold parameterDerivativeIntegrand
  exact measurable_const.div
    (measurable_const.add
      (measurable_const.mul (htan.pow_const 2)))

private theorem parameterDerivativeIntegrand_norm_le_one (x a : ℝ) :
    ‖parameterDerivativeIntegrand x a‖ ≤ (1 : ℝ) := by
  have hprod : 0 ≤ a ^ 2 * Real.tan x ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hden : 1 ≤ 1 + a ^ 2 * Real.tan x ^ 2 := by linarith
  have hdenpos : 0 < 1 + a ^ 2 * Real.tan x ^ 2 := by linarith
  rw [Real.norm_eq_abs]
  unfold parameterDerivativeIntegrand
  rw [abs_of_pos (one_div_pos.mpr hdenpos)]
  exact (div_le_one hdenpos).2 hden

private theorem integrand_hasDerivAt_parameter (x a : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s => integrand x s)
      (parameterDerivativeIntegrand x a) a := by
  have htanpos : 0 < Real.tan x :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2
  have htanne : Real.tan x ≠ 0 := htanpos.ne'
  have hinner :
      HasDerivAt (fun s : ℝ => s * Real.tan x) (Real.tan x) a := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id a).mul_const (Real.tan x)
  have hraw :=
    ((Real.hasDerivAt_arctan (a * Real.tan x)).comp a hinner).div_const
      (Real.tan x)
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hxpi : x ≠ Real.pi / 2 := ne_of_lt hx.2
  simp only [integrand, hx0, hxpi, if_false]
  unfold parameterDerivativeIntegrand
  convert hraw using 1
  field_simp [htanne]

private theorem integralFunction_hasDerivAt (a : ℝ) :
    HasDerivAt integralFunction
      (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) a := by
  have hF_meas :
      ∀ᶠ s in 𝓝 a,
        AEStronglyMeasurable (fun x : ℝ => integrand x s)
          (volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))) :=
    Eventually.of_forall fun s => (measurable_integrand s).aestronglyMeasurable
  have hF_int :
      IntervalIntegrable (fun x : ℝ => integrand x a) volume
        0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (half_pos Real.pi_pos).le] using gap3 a
  have hF'_meas :
      AEStronglyMeasurable
        (fun x : ℝ => parameterDerivativeIntegrand x a)
        (volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))) :=
    (measurable_parameterDerivativeIntegrand a).aestronglyMeasurable
  have h_bound :
      ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
        ∀ s ∈ Set.univ,
          ‖parameterDerivativeIntegrand x s‖ ≤ (fun _x : ℝ => (1 : ℝ)) x :=
    Eventually.of_forall fun x _ s _ =>
      parameterDerivativeIntegrand_norm_le_one x s
  have hbound_int :
      IntervalIntegrable (fun _x : ℝ => (1 : ℝ)) volume
        0 (Real.pi / 2) :=
    continuous_const.intervalIntegrable 0 (Real.pi / 2)
  have h_diff :
      ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
        ∀ s ∈ Set.univ,
          HasDerivAt (fun s => integrand x s)
            (parameterDerivativeIntegrand x s) s := by
    filter_upwards
      [volume.ae_ne (0 : ℝ),
        volume.ae_ne (Real.pi / 2 : ℝ)] with x hx0 hxpi
    intro hx s _
    rw [Set.uIoc_of_le (half_pos Real.pi_pos).le] at hx
    exact integrand_hasDerivAt_parameter x s
      ⟨hx.1, lt_of_le_of_ne hx.2 hxpi⟩
  have h :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (a := (0 : ℝ)) (b := Real.pi / 2) (μ := volume)
      (F := fun s x => integrand x s)
      (F' := fun s x => parameterDerivativeIntegrand x s)
      (bound := fun _x : ℝ => (1 : ℝ))
      (x₀ := a) (s := Set.univ)
      Filter.univ_mem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa only [integralFunction] using h.2

theorem gap7 (a : ℝ) :
    deriv integralFunction a =
      ∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a :=
  (integralFunction_hasDerivAt a).deriv

private def smoothParameterKernel (a x : ℝ) : ℝ :=
  if a = 0 then 1
  else
    Real.cos x ^ 2 /
      (Real.cos x ^ 2 + a ^ 2 * Real.sin x ^ 2)

private def rationalKernel (a t : ℝ) : ℝ :=
  1 / ((1 + t ^ 2) * (1 + a ^ 2 * t ^ 2))

private theorem smoothParameterKernel_continuous (a : ℝ) :
    Continuous (smoothParameterKernel a) := by
  by_cases ha : a = 0
  · subst a
    have heq : smoothParameterKernel 0 = fun _x : ℝ => (1 : ℝ) := by
      funext x
      simp [smoothParameterKernel]
    rw [heq]
    fun_prop
  · unfold smoothParameterKernel
    simp only [ha, if_false]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
      have htrig := Real.sin_sq_add_cos_sq x
      by_cases hcos : Real.cos x = 0
      · have hsin : Real.sin x ^ 2 = 1 := by
          rw [hcos] at htrig
          norm_num at htrig ⊢
          exact htrig
        have hpos :
            0 < Real.cos x ^ 2 + a ^ 2 * Real.sin x ^ 2 := by
          rw [hcos, hsin]
          norm_num
          exact ha2
        exact hpos.ne'
      · have hcos2 : 0 < Real.cos x ^ 2 := sq_pos_of_ne_zero hcos
        have hmul : 0 ≤ a ^ 2 * Real.sin x ^ 2 :=
          mul_nonneg (sq_nonneg _) (sq_nonneg _)
        exact (add_pos_of_pos_of_nonneg hcos2 hmul).ne'

private theorem parameterDerivativeIntegral_eq_smooth (a : ℝ) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) =
      ∫ x in (0 : ℝ)..Real.pi / 2, smoothParameterKernel a x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (Real.pi / 2 : ℝ)] with x hxpi hx
  by_cases ha : a = 0
  · simp [parameterDerivativeIntegrand, smoothParameterKernel, ha]
  · have hx' : x ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
      simpa [Set.uIoc_of_le (half_pos Real.pi_pos).le] using hx
    have hxlt : x < Real.pi / 2 := lt_of_le_of_ne hx'.2 hxpi
    have hleft : -(Real.pi / 2) < x := by
      linarith [hx'.1, half_pos Real.pi_pos]
    have hcos : Real.cos x ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨hleft, hxlt⟩).ne'
    unfold parameterDerivativeIntegrand smoothParameterKernel
    simp only [ha, if_false]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]

private theorem rationalKernel_integrable (a : ℝ) :
    IntegrableOn (rationalKernel a) (Set.Ioi (0 : ℝ)) := by
  have hmeas :
      AEStronglyMeasurable (rationalKernel a)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Continuous.aestronglyMeasurable
    unfold rationalKernel
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      have h₁ : 0 < 1 + t ^ 2 := by positivity
      have h₂ : 0 < 1 + a ^ 2 * t ^ 2 := by positivity
      exact mul_ne_zero h₁.ne' h₂.ne'
  apply integrable_inv_one_add_sq.integrableOn.mono' hmeas
  filter_upwards [] with t
  have h₁ : 0 < 1 + t ^ 2 := by positivity
  have h₂ : 0 < 1 + a ^ 2 * t ^ 2 := by positivity
  have hk : 0 ≤ rationalKernel a t := by
    unfold rationalKernel
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hk]
  unfold rationalKernel
  have heq :
      1 / ((1 + t ^ 2) * (1 + a ^ 2 * t ^ 2)) =
        (1 + t ^ 2)⁻¹ * (1 + a ^ 2 * t ^ 2)⁻¹ := by
    field_simp [h₁.ne', h₂.ne']
  rw [heq]
  have hinv : (1 + a ^ 2 * t ^ 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ h₂).2 (by
      have hm : 0 ≤ a ^ 2 * t ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hinv (inv_nonneg.mpr h₁.le)

private theorem smoothParameterKernel_arctan (a t : ℝ) :
    smoothParameterKernel a (Real.arctan t) *
        (1 / (1 + t ^ 2)) =
      rationalKernel a t := by
  have hq : 0 < Real.sqrt (1 + t ^ 2) := by positivity
  by_cases ha : a = 0
  · simp [smoothParameterKernel, rationalKernel, ha]
  · unfold smoothParameterKernel rationalKernel
    simp only [ha, if_false]
    rw [Real.sin_arctan, Real.cos_arctan]
    field_simp [hq.ne']

private theorem parameterDerivativeIntegral_eq_improper (a : ℝ) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) =
      improperRationalIntegral a := by
  let g : ℝ → ℝ := smoothParameterKernel a
  let h : ℝ → ℝ := rationalKernel a
  have hg : Continuous g := smoothParameterKernel_continuous a
  have hhint : IntegrableOn h (Set.Ioi (0 : ℝ)) := by
    simpa only [h] using rationalKernel_integrable a
  have hfinite (R : ℝ) :
      (∫ t in (0 : ℝ)..R, h t) =
        ∫ x in (0 : ℝ)..Real.arctan R, g x := by
    have hsub :=
      intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := R)
        (f := Real.arctan)
        (f' := fun t : ℝ => 1 / (1 + t ^ 2))
        (g := g)
        (fun t _ => by
          simpa [one_div] using Real.hasDerivAt_arctan t)
        (by
          apply Continuous.continuousOn
          apply Continuous.div
          · fun_prop
          · fun_prop
          · intro t
            positivity)
        hg
    rw [Real.arctan_zero] at hsub
    calc
      (∫ t in (0 : ℝ)..R, h t) =
          ∫ t in (0 : ℝ)..R,
            (g ∘ Real.arctan) t * (1 / (1 + t ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [g, h, Function.comp_apply]
        exact (smoothParameterKernel_arctan a t).symm
      _ = ∫ x in (0 : ℝ)..Real.arctan R, g x := hsub
  have hleft :
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, h t) atTop
        (𝓝 (∫ t in Set.Ioi (0 : ℝ), h t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hhint tendsto_id
  have hprimitive :
      Continuous (fun u => ∫ x in (0 : ℝ)..u, g x) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hg.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hright :
      Tendsto (fun R => ∫ x in (0 : ℝ)..Real.arctan R, g x)
        atTop (𝓝 (∫ x in (0 : ℝ)..Real.pi / 2, g x)) :=
    hprimitive.continuousAt.tendsto.comp
      (Real.tendsto_arctan_atTop.mono_right inf_le_left)
  have hevent :
      (fun R => ∫ t in (0 : ℝ)..R, h t) =ᶠ[atTop]
        fun R => ∫ x in (0 : ℝ)..Real.arctan R, g x :=
    Eventually.of_forall hfinite
  have hlim :
      (∫ t in Set.Ioi (0 : ℝ), h t) =
        ∫ x in (0 : ℝ)..Real.pi / 2, g x :=
    tendsto_nhds_unique hleft (hright.congr' hevent.symm)
  rw [parameterDerivativeIntegral_eq_smooth]
  unfold improperRationalIntegral
  simpa only [g, h, rationalKernel] using hlim.symm

theorem gap8 (a : ℝ) (ha : a ^ 2 ≠ 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) =
      improperRationalIntegral a :=
  parameterDerivativeIntegral_eq_improper a

private theorem parameterDerivativeIntegral_value (a : ℝ) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) =
      Real.pi / (2 * (1 + |a|)) := by
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) =
        ∫ x in (0 : ℝ)..Real.pi / 2, parameterKernel |a| x := by
      apply intervalIntegral.integral_congr
      intro x _
      simp [parameterDerivativeIntegrand, parameterKernel, sq_abs]
    _ = Real.pi / (2 * (1 + |a|)) :=
      parameterKernel_integral_value |a| (abs_nonneg a)

theorem gap9 (a : ℝ) (ha : a ^ 2 ≠ 1) :
    improperRationalIntegral a =
      Real.pi / (2 * (1 + |a|)) := by
  rw [← parameterDerivativeIntegral_eq_improper a]
  exact parameterDerivativeIntegral_value a

theorem gap10 (a : ℝ) (ha : a ^ 2 ≠ 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) =
      Real.pi / (2 * (1 + |a|)) :=
  parameterDerivativeIntegral_value a

theorem gap11 (a : ℝ) (ha : a ^ 2 = 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) =
      ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 2 := by
  have habs : |a| = 1 := by
    have habssq : |a| ^ 2 = 1 := by simpa [sq_abs] using ha
    nlinarith [abs_nonneg a]
  rw [parameterDerivativeIntegral_value, habs, integral_cos_sq]
  simp
  ring

theorem gap12 (a : ℝ) (ha : a ^ 2 = 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 2) =
      Real.pi / 4 := by
  rw [integral_cos_sq]
  simp
  ring

theorem gap13 (a : ℝ) (ha : a ^ 2 = 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        parameterDerivativeIntegrand x a) =
      Real.pi / 4 := by
  rw [gap11 a ha, gap12 a ha]

theorem gap14 (a : ℝ) :
    deriv integralFunction a =
      Real.pi / (2 * (1 + |a|)) := by
  rw [gap7, parameterDerivativeIntegral_value]

theorem gap15 :
    ∀ a : ℝ, 0 < a →
      integralFunction a =
        (Real.pi / 2) * Real.log (1 + a) + positiveConstant := by
  intro a ha
  rw [integralFunction_formula, Real.sign_of_pos ha, abs_of_pos ha]
  simp [positiveConstant]

theorem gap16 :
    ∀ a : ℝ, a < 0 →
      integralFunction a =
        -(Real.pi / 2) * Real.log (1 - a) + negativeConstant := by
  intro a ha
  rw [integralFunction_formula, Real.sign_of_neg ha, abs_of_neg ha]
  simp [negativeConstant]
  ring

private theorem integralFunction_tendsto_zero_right :
    Tendsto integralFunction (𝓝[>] (0 : ℝ))
      (𝓝 (integralFunction 0)) := by
  have hcont :
      ContinuousAt
        (fun a : ℝ =>
          (Real.pi / 2) * Real.log (1 + a) + positiveConstant) 0 := by
    unfold positiveConstant
    exact
      (continuousAt_const.mul
        ((continuousAt_const.add continuousAt_id).log (by norm_num))).add
        continuousAt_const
  have hlim :
      Tendsto
        (fun a : ℝ =>
          (Real.pi / 2) * Real.log (1 + a) + positiveConstant)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h :
        Tendsto
          (fun a : ℝ =>
            (Real.pi / 2) * Real.log (1 + a) + positiveConstant)
          (𝓝[>] (0 : ℝ))
          (𝓝 ((Real.pi / 2) * Real.log (1 + 0) + positiveConstant)) :=
      hcont.tendsto.mono_left inf_le_left
    simpa [positiveConstant] using h
  have heq :
      integralFunction =ᶠ[𝓝[>] (0 : ℝ)]
        fun a : ℝ =>
          (Real.pi / 2) * Real.log (1 + a) + positiveConstant := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact gap15 a ha
  have hzero : integralFunction 0 = 0 := by
    simp [integralFunction_formula]
  rw [hzero]
  exact hlim.congr' heq.symm

private theorem integralFunction_tendsto_zero_left :
    Tendsto integralFunction (𝓝[<] (0 : ℝ))
      (𝓝 (integralFunction 0)) := by
  have hcont :
      ContinuousAt
        (fun a : ℝ =>
          -(Real.pi / 2) * Real.log (1 - a) + negativeConstant) 0 := by
    unfold negativeConstant
    exact
      (continuousAt_const.mul
        ((continuousAt_const.sub continuousAt_id).log (by norm_num))).add
        continuousAt_const
  have hlim :
      Tendsto
        (fun a : ℝ =>
          -(Real.pi / 2) * Real.log (1 - a) + negativeConstant)
        (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    have h :
        Tendsto
          (fun a : ℝ =>
            -(Real.pi / 2) * Real.log (1 - a) + negativeConstant)
          (𝓝[<] (0 : ℝ))
          (𝓝 (-(Real.pi / 2) * Real.log (1 - 0) + negativeConstant)) :=
      hcont.tendsto.mono_left inf_le_left
    simpa [negativeConstant] using h
  have heq :
      integralFunction =ᶠ[𝓝[<] (0 : ℝ)]
        fun a : ℝ =>
          -(Real.pi / 2) * Real.log (1 - a) + negativeConstant := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact gap16 a ha
  have hzero : integralFunction 0 = 0 := by
    simp [integralFunction_formula]
  rw [hzero]
  exact hlim.congr' heq.symm

theorem gap17 :
    Tendsto integralFunction (𝓝[>] (0 : ℝ))
        (𝓝 (integralFunction 0)) ↔
      Tendsto integralFunction (𝓝[<] (0 : ℝ))
        (𝓝 (integralFunction 0)) :=
  iff_of_true integralFunction_tendsto_zero_right
    integralFunction_tendsto_zero_left

theorem gap18 :
    Tendsto integralFunction (𝓝[<] (0 : ℝ))
      (𝓝 (integralFunction 0)) :=
  integralFunction_tendsto_zero_left

theorem gap19 :
    Tendsto integralFunction (𝓝[>] (0 : ℝ))
      (𝓝 (integralFunction 0)) :=
  integralFunction_tendsto_zero_right

theorem gap20 :
    integralFunction 0 = 0 := by
  simp [integralFunction_formula]

theorem gap21 :
    positiveConstant = 0 := by
  rfl

theorem gap22 :
    negativeConstant = 0 := by
  rfl

theorem gap23 (a : ℝ) :
    integralFunction a =
      (Real.pi / 2) * Real.sign a * Real.log (1 + |a|) :=
  integralFunction_formula a

end

end ProofGap.Exercise3734
