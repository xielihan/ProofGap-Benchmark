import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3736

noncomputable section

open Filter
open scoped Interval Topology

def originalIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Real.arctan x / x) * (1 / Real.sqrt (1 - x ^ 2))

def doubleIntegralXY : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (1 / Real.sqrt (1 - x ^ 2)) *
      ∫ y in (0 : ℝ)..1, 1 / (1 + x ^ 2 * y ^ 2)

def doubleIntegralYX : ℝ :=
  ∫ y in (0 : ℝ)..1,
    ∫ x in (0 : ℝ)..1,
      1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2))

def innerIntegral (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2))

def trigonometricIntegral (y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi / 2, 1 / (1 + y ^ 2 * Real.cos t ^ 2)

def trigonometricPrimitive (y t : ℝ) : ℝ :=
  (1 / Real.sqrt (1 + y ^ 2)) *
    Real.arctan (Real.tan t / Real.sqrt (1 + y ^ 2))

def logarithmicPrimitive (y : ℝ) : ℝ :=
  (Real.pi / 2) * Real.log (y + Real.sqrt (1 + y ^ 2))

private def rationalFactor (y x : ℝ) : ℝ :=
  1 / (1 + x ^ 2 * y ^ 2)

private def weightedIntegrand (y x : ℝ) : ℝ :=
  rationalFactor y x * (Real.sqrt (1 - x ^ 2))⁻¹

private theorem rationalFactor_continuous (y : ℝ) :
    Continuous (rationalFactor y) := by
  unfold rationalFactor
  exact continuous_const.div
    (continuous_const.add ((continuous_id.pow 2).mul continuous_const))
    (fun x => by positivity)

private theorem weightedIntegrand_eq (y x : ℝ) :
    weightedIntegrand y x =
      1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2)) := by
  unfold weightedIntegrand rationalFactor
  simp only [one_div, mul_inv_rev]

private theorem weighted_intervalIntegrable (y : ℝ) :
    IntervalIntegrable (weightedIntegrand y) MeasureTheory.volume (-1) 1 := by
  simpa [weightedIntegrand] using
    Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul
      (rationalFactor_continuous y).continuousOn

private theorem weighted_even (y x : ℝ) :
    weightedIntegrand y (-x) = weightedIntegrand y x := by
  unfold weightedIntegrand rationalFactor
  ring_nf

private theorem trig_even_about_half (y t : ℝ) :
    1 / (1 + y ^ 2 * Real.cos (Real.pi - t) ^ 2) =
      1 / (1 + y ^ 2 * Real.cos t ^ 2) := by
  rw [Real.cos_pi_sub]
  ring_nf

private theorem weighted_full_eq_two_half (y : ℝ) :
    (∫ x in (-1 : ℝ)..1, weightedIntegrand y x) =
      2 * ∫ x in (0 : ℝ)..1, weightedIntegrand y x := by
  have hint := weighted_intervalIntegrable y
  have hneg :
      (∫ x in (-1 : ℝ)..0, weightedIntegrand y x) =
        ∫ x in (0 : ℝ)..1, weightedIntegrand y x := by
    calc
      (∫ x in (-1 : ℝ)..0, weightedIntegrand y x) =
          ∫ x in (0 : ℝ)..1, weightedIntegrand y (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (a := (0 : ℝ)) (b := 1) (weightedIntegrand y)).symm
      _ = ∫ x in (0 : ℝ)..1, weightedIntegrand y x := by
        apply intervalIntegral.integral_congr
        intro x _
        exact weighted_even y x
  have hleft : IntervalIntegrable (weightedIntegrand y)
      MeasureTheory.volume (-1) 0 :=
    hint.mono (by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨hx.1, hx.2.trans (by norm_num)⟩) (le_refl _)
  have hright : IntervalIntegrable (weightedIntegrand y)
      MeasureTheory.volume 0 1 :=
    hint.mono (by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨(by linarith [hx.1]), hx.2⟩) (le_refl _)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  rw [hneg]
  ring

private theorem trig_full_eq_two_half (y : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi,
      1 / (1 + y ^ 2 * Real.cos t ^ 2)) =
      2 * ∫ t in (0 : ℝ)..Real.pi / 2,
        1 / (1 + y ^ 2 * Real.cos t ^ 2) := by
  let q : ℝ → ℝ := fun t => 1 / (1 + y ^ 2 * Real.cos t ^ 2)
  change (∫ t in (0 : ℝ)..Real.pi, q t) =
    2 * ∫ t in (0 : ℝ)..Real.pi / 2, q t
  have hq : Continuous q := by
    exact continuous_const.div
      (continuous_const.add
        (continuous_const.mul (Real.continuous_cos.pow 2)))
      (fun t => by positivity)
  have hsecond :
      (∫ t in Real.pi / 2..Real.pi, q t) =
        ∫ t in (0 : ℝ)..Real.pi / 2, q t := by
    calc
      (∫ t in Real.pi / 2..Real.pi, q t) =
          ∫ t in (0 : ℝ)..Real.pi / 2, q (Real.pi - t) := by
        have hcomp := intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := Real.pi / 2) q Real.pi
        rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
          sub_zero] at hcomp
        exact hcomp.symm
      _ = ∫ t in (0 : ℝ)..Real.pi / 2, q t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact trig_even_about_half y t
  have hfirstInt : IntervalIntegrable q MeasureTheory.volume
      (0 : ℝ) (Real.pi / 2) :=
    hq.intervalIntegrable (0 : ℝ) (Real.pi / 2)
  have hsecondInt : IntervalIntegrable q MeasureTheory.volume
      (Real.pi / 2) Real.pi :=
    hq.intervalIntegrable (Real.pi / 2) Real.pi
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hfirstInt hsecondInt]
  rw [hsecond]
  ring

theorem gap3 (y : ℝ) :
    innerIntegral y = trigonometricIntegral y := by
  have hcheb :=
    Polynomial.Chebyshev.integral_measureT_eq_integral_cos_of_continuous
      (rationalFactor_continuous y).continuousOn
  rw [Polynomial.Chebyshev.integral_measureT] at hcheb
  have hfull :
      (∫ x in (-1 : ℝ)..1, weightedIntegrand y x) =
        ∫ t in (0 : ℝ)..Real.pi,
          1 / (1 + y ^ 2 * Real.cos t ^ 2) := by
    simpa [weightedIntegrand, rationalFactor, mul_comm] using hcheb
  have htwo := (weighted_full_eq_two_half y).symm.trans
    (hfull.trans (trig_full_eq_two_half y))
  have hhalf :
      (∫ x in (0 : ℝ)..1, weightedIntegrand y x) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          1 / (1 + y ^ 2 * Real.cos t ^ 2) := by
    linarith
  unfold innerIntegral trigonometricIntegral
  rw [← hhalf]
  apply intervalIntegral.integral_congr
  intro x _
  exact (weightedIntegrand_eq y x).symm

private theorem trigonometricPrimitive_deriv (y t : ℝ)
    (hcos : Real.cos t ≠ 0) :
    HasDerivAt (trigonometricPrimitive y)
      (1 / (1 + y ^ 2 * Real.cos t ^ 2)) t := by
  have hspos : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsne : Real.sqrt (1 + y ^ 2) ≠ 0 := ne_of_gt hspos
  have hssq : Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 :=
    Real.sq_sqrt (by positivity)
  have htan := Real.hasDerivAt_tan hcos
  have hinner := htan.div_const (Real.sqrt (1 + y ^ 2))
  have harctan :=
    (Real.hasDerivAt_arctan
      (Real.tan t / Real.sqrt (1 + y ^ 2))).comp t hinner
  have h := harctan.const_mul (1 / Real.sqrt (1 + y ^ 2))
  unfold trigonometricPrimitive
  convert h using 1
  simp only [one_div]
  rw [Real.tan_eq_sin_div_cos]
  have htrig := Real.sin_sq_add_cos_sq t
  field_simp [hsne, hcos]
  nlinarith

private theorem trigonometricPrimitive_limit (y : ℝ) :
    Tendsto (trigonometricPrimitive y)
      (𝓝[<] (Real.pi / 2))
      (𝓝 (Real.pi / (2 * Real.sqrt (1 + y ^ 2)))) := by
  have hspos : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsne : Real.sqrt (1 + y ^ 2) ≠ 0 := ne_of_gt hspos
  have htan : Tendsto
      (fun t : ℝ => Real.tan t / Real.sqrt (1 + y ^ 2))
      (𝓝[<] (Real.pi / 2)) atTop :=
    Filter.Tendsto.atTop_div_const hspos Real.tendsto_tan_pi_div_two
  have harctan :
      Tendsto
        (fun t : ℝ =>
          Real.arctan (Real.tan t / Real.sqrt (1 + y ^ 2)))
        (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp htan).mono_right inf_le_left
  unfold trigonometricPrimitive
  convert harctan.const_mul (1 / Real.sqrt (1 + y ^ 2)) using 1
  field_simp [hsne]

private theorem trigonometricPrimitive_zero (y : ℝ) :
    trigonometricPrimitive y 0 = 0 := by
  simp [trigonometricPrimitive]

private theorem trigonometricIntegral_value (y : ℝ) :
    trigonometricIntegral y =
      Real.pi / (2 * Real.sqrt (1 + y ^ 2)) := by
  let q : ℝ → ℝ := fun t => 1 / (1 + y ^ 2 * Real.cos t ^ 2)
  have hq : Continuous q := by
    exact continuous_const.div
      (continuous_const.add
        (continuous_const.mul (Real.continuous_cos.pow 2)))
      (fun t => by positivity)
  have hleft :
      Tendsto (trigonometricPrimitive y) (𝓝[>] (0 : ℝ))
        (𝓝 (trigonometricPrimitive y 0)) := by
    have hderiv0 := trigonometricPrimitive_deriv y 0 (by norm_num)
    exact hderiv0.continuousAt.tendsto.mono_left inf_le_left
  have hright := trigonometricPrimitive_limit y
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (b := Real.pi / 2) (by positivity)
    (fun t ht => by
      apply trigonometricPrimitive_deriv
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩))
    (hq.intervalIntegrable (0 : ℝ) (Real.pi / 2)) hleft hright
  unfold trigonometricIntegral
  rw [hi, trigonometricPrimitive_zero]
  ring

theorem gap4 (y : ℝ) :
    ∃ L : ℝ,
      Tendsto (trigonometricPrimitive y)
          (𝓝[<] (Real.pi / 2)) (𝓝 L) ∧
        trigonometricIntegral y = L - trigonometricPrimitive y 0 := by
  refine ⟨Real.pi / (2 * Real.sqrt (1 + y ^ 2)),
    trigonometricPrimitive_limit y, ?_⟩
  rw [trigonometricIntegral_value y, trigonometricPrimitive_zero]
  ring

theorem gap5 (y : ℝ) :
    Tendsto (trigonometricPrimitive y)
        (𝓝[<] (Real.pi / 2))
        (𝓝 (Real.pi / (2 * Real.sqrt (1 + y ^ 2)))) ∧
      trigonometricPrimitive y 0 = 0 :=
  ⟨trigonometricPrimitive_limit y, trigonometricPrimitive_zero y⟩

theorem gap6 (y : ℝ) :
    innerIntegral y = Real.pi / (2 * Real.sqrt (1 + y ^ 2)) :=
  (gap3 y).trans (trigonometricIntegral_value y)

private theorem logarithmicPrimitive_deriv (y : ℝ) :
    HasDerivAt logarithmicPrimitive
      (Real.pi / (2 * Real.sqrt (1 + y ^ 2))) y := by
  unfold logarithmicPrimitive
  change HasDerivAt
    (fun t : ℝ => (Real.pi / 2) * Real.arsinh t)
    (Real.pi / (2 * Real.sqrt (1 + y ^ 2))) y
  convert (Real.hasDerivAt_arsinh y).const_mul (Real.pi / 2) using 1
  ring

theorem gap8 :
    (∫ y in (0 : ℝ)..1, Real.pi / (2 * Real.sqrt (1 + y ^ 2))) =
      logarithmicPrimitive 1 - logarithmicPrimitive 0 := by
  have hcont : Continuous
      (fun y : ℝ => Real.pi / (2 * Real.sqrt (1 + y ^ 2))) := by
    exact continuous_const.div
      (continuous_const.mul
        ((continuous_const.add (continuous_id.pow 2)).sqrt))
      (fun y => by
        have : 0 < Real.sqrt (1 + y ^ 2) :=
          Real.sqrt_pos.2 (by positivity)
        positivity)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => logarithmicPrimitive_deriv y)
    (hcont.intervalIntegrable (0 : ℝ) 1)

theorem gap9 :
    logarithmicPrimitive 1 - logarithmicPrimitive 0 =
      (Real.pi / 2) * Real.log (1 + Real.sqrt 2) := by
  unfold logarithmicPrimitive
  norm_num

private theorem arctan_quotient_eq_integral (x : ℝ) (hx : x ≠ 0) :
    Real.arctan x / x =
      ∫ y in (0 : ℝ)..1, 1 / (1 + x ^ 2 * y ^ 2) := by
  let A : ℝ → ℝ := fun y => Real.arctan (x * y) / x
  have hderiv : ∀ y : ℝ,
      HasDerivAt A (1 / (1 + x ^ 2 * y ^ 2)) y := by
    intro y
    have hlin : HasDerivAt (fun t : ℝ => x * t) x y :=
      by
        convert (hasDerivAt_id y).const_mul x using 1 <;> simp
    have h := ((Real.hasDerivAt_arctan (x * y)).comp y hlin).div_const x
    dsimp [A]
    convert h using 1
    field_simp [hx]
  have hcont : Continuous
      (fun y : ℝ => 1 / (1 + x ^ 2 * y ^ 2)) := by
    exact continuous_const.div
      (continuous_const.add
        (continuous_const.mul (continuous_id.pow 2)))
      (fun y => by positivity)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hderiv y) (hcont.intervalIntegrable (0 : ℝ) 1)
  dsimp [A] at hi
  simpa using hi.symm

theorem gap1 :
    originalIntegral = doubleIntegralXY := by
  unfold originalIntegral doubleIntegralXY
  rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one),
    intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  rw [arctan_quotient_eq_integral x (ne_of_gt hx.1)]
  ring

private theorem doubleIntegrand_integrable :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ =>
        1 / (Real.sqrt (1 - p.1 ^ 2) * (1 + p.1 ^ 2 * p.2 ^ 2)))
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have hxInterval : IntervalIntegrable
      (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹)
      MeasureTheory.volume 0 1 :=
    by
      simpa only [Real.sqrt_inv] using
        Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv.mono
          (c := (0 : ℝ)) (d := 1)
          (by
            intro x hx
            rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
            rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
            exact ⟨by linarith [hx.1], hx.2⟩)
          (le_refl _)
  have hxint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹)
      (Set.Ioc (0 : ℝ) 1) := hxInterval.1
  have hyint : MeasureTheory.IntegrableOn
      (fun _y : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
    MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
  have hdom : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Real.sqrt (1 - p.1 ^ 2))⁻¹)
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    unfold MeasureTheory.IntegrableOn at hxint hyint ⊢
    rw [← MeasureTheory.Measure.prod_restrict]
    simpa using hxint.mul_prod hyint
  have hrect :
      MeasurableSet (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  apply hdom.mono'
  · have hden : Continuous (fun p : ℝ × ℝ =>
        Real.sqrt (1 - p.1 ^ 2) * (1 + p.1 ^ 2 * p.2 ^ 2)) :=
      (Real.continuous_sqrt.comp
        (continuous_const.sub (continuous_fst.pow 2))).mul
        (continuous_const.add ((continuous_fst.pow 2).mul
          (continuous_snd.pow 2)))
    simpa only [one_div] using hden.measurable.inv.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem hrect] with p hp
    have hsqrtNonneg : 0 ≤ Real.sqrt (1 - p.1 ^ 2) :=
      Real.sqrt_nonneg _
    have hprod : 0 ≤ p.1 ^ 2 * p.2 ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hfactor : 1 ≤ 1 + p.1 ^ 2 * p.2 ^ 2 := by linarith
    have hnonneg :
        0 ≤ 1 /
          (Real.sqrt (1 - p.1 ^ 2) * (1 + p.1 ^ 2 * p.2 ^ 2)) := by
      rw [one_div]
      exact inv_nonneg.mpr (mul_nonneg hsqrtNonneg (by positivity))
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    by_cases hone : p.1 = 1
    · rw [hone]
      norm_num
    · have hxlt : p.1 < 1 := lt_of_le_of_ne hp.1.2 hone
      have hrad : 0 < 1 - p.1 ^ 2 := by nlinarith [hp.1.1]
      have hsqrtPos : 0 < Real.sqrt (1 - p.1 ^ 2) :=
        Real.sqrt_pos.2 hrad
      rw [one_div, mul_inv_rev]
      have hInv : (1 + p.1 ^ 2 * p.2 ^ 2)⁻¹ ≤ 1 := by
        exact (inv_le_one₀ (by positivity)).2 hfactor
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hInv (inv_nonneg.mpr hsqrtPos.le)

private theorem doubleIntegralXY_eq_YX :
    doubleIntegralXY = doubleIntegralYX := by
  let f : ℝ × ℝ → ℝ := fun p =>
    1 / (Real.sqrt (1 - p.1 ^ 2) * (1 + p.1 ^ 2 * p.2 ^ 2))
  have hrect :
      MeasurableSet (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hind : MeasureTheory.Integrable
      ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1).indicator f)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    rw [MeasureTheory.integrable_indicator_iff hrect]
    exact doubleIntegrand_integrable
  let g : ℝ → ℝ → ℝ := fun x y =>
    (Set.Ioc (0 : ℝ) 1).indicator
      (fun x => (Set.Ioc (0 : ℝ) 1).indicator
        (fun y => 1 /
          (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2))) y) x
  have huncurry : Function.uncurry g =
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1).indicator f := by
    funext p
    by_cases hx : p.1 ∈ Set.Ioc (0 : ℝ) 1
    · by_cases hy : p.2 ∈ Set.Ioc (0 : ℝ) 1
      · simp [Function.uncurry, g, f, hx, hy]
      · simp [Function.uncurry, g, f, hx, hy]
    · simp [Function.uncurry, g, f, hx]
  have hg : MeasureTheory.Integrable (Function.uncurry g)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    rw [huncurry]
    exact hind
  have hswap :
      (∫ x : ℝ, ∫ y : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ y : ℝ, ∫ x : ℝ, g x y
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.integral_integral_swap hg
  have hleft :
      (∫ x : ℝ, ∫ y : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ x in Set.Ioc (0 : ℝ) 1,
          ∫ y in Set.Ioc (0 : ℝ) 1,
            1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2)) := by
    calc
      (∫ x : ℝ, ∫ y : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
            (fun x => ∫ y : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun y => 1 /
                (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2))) y
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) x
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
        · simp [g, hx]
        · simp [g, hx]
      _ = ∫ x in Set.Ioc (0 : ℝ) 1,
            ∫ y : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun y => 1 /
                (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2))) y
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        exact MeasureTheory.integral_indicator measurableSet_Ioc
      _ = ∫ x in Set.Ioc (0 : ℝ) 1,
            ∫ y in Set.Ioc (0 : ℝ) 1,
              1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        exact MeasureTheory.integral_indicator measurableSet_Ioc
  have hright :
      (∫ y : ℝ, ∫ x : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ y in Set.Ioc (0 : ℝ) 1,
          ∫ x in Set.Ioc (0 : ℝ) 1,
            1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2)) := by
    calc
      (∫ y : ℝ, ∫ x : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ y : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
            (fun y => ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun x => 1 /
                (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2))) x
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) y
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ Set.Ioc (0 : ℝ) 1
        · simp [g, hy]
        · simp [g, hy]
      _ = ∫ y in Set.Ioc (0 : ℝ) 1,
            ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun x => 1 /
                (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2))) x
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        exact MeasureTheory.integral_indicator measurableSet_Ioc
      _ = ∫ y in Set.Ioc (0 : ℝ) 1,
            ∫ x in Set.Ioc (0 : ℝ) 1,
              1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        exact MeasureTheory.integral_indicator measurableSet_Ioc
  unfold doubleIntegralXY doubleIntegralYX
  rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one),
    intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]
  calc
    (∫ x in Set.Ioc (0 : ℝ) 1,
      (1 / Real.sqrt (1 - x ^ 2)) *
        ∫ y in (0 : ℝ)..1, 1 / (1 + x ^ 2 * y ^ 2)) =
        ∫ x in Set.Ioc (0 : ℝ) 1,
          ∫ y in Set.Ioc (0 : ℝ) 1,
            1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]
      calc
        (1 / Real.sqrt (1 - x ^ 2)) *
            ∫ y in Set.Ioc (0 : ℝ) 1, 1 / (1 + x ^ 2 * y ^ 2) =
            ∫ y in Set.Ioc (0 : ℝ) 1,
              (1 / Real.sqrt (1 - x ^ 2)) *
                (1 / (1 + x ^ 2 * y ^ 2)) := by
          rw [MeasureTheory.integral_const_mul]
        _ = ∫ y in Set.Ioc (0 : ℝ) 1,
              1 / (Real.sqrt (1 - x ^ 2) *
                (1 + x ^ 2 * y ^ 2)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with y
          simp only [one_div, mul_inv_rev]
          ring
    _ = ∫ y in Set.Ioc (0 : ℝ) 1,
          ∫ x in Set.Ioc (0 : ℝ) 1,
            1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2)) :=
      hleft.symm.trans (hswap.trans hright)
    _ = ∫ y in Set.Ioc (0 : ℝ) 1,
          ∫ x in (0 : ℝ)..1,
            1 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 * y ^ 2)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]

theorem gap2 :
    originalIntegral = doubleIntegralYX :=
  gap1.trans doubleIntegralXY_eq_YX

theorem gap7 :
    originalIntegral =
      ∫ y in (0 : ℝ)..1, Real.pi / (2 * Real.sqrt (1 + y ^ 2)) := by
  rw [gap2]
  unfold doubleIntegralYX
  apply intervalIntegral.integral_congr
  intro y _
  exact gap6 y

theorem gap10 :
    originalIntegral =
      (Real.pi / 2) * Real.log (1 + Real.sqrt 2) := by
  calc
    originalIntegral =
        ∫ y in (0 : ℝ)..1,
          Real.pi / (2 * Real.sqrt (1 + y ^ 2)) := gap7
    _ = logarithmicPrimitive 1 - logarithmicPrimitive 0 := gap8
    _ = (Real.pi / 2) * Real.log (1 + Real.sqrt 2) := gap9

end

end ProofGap.Exercise3736
