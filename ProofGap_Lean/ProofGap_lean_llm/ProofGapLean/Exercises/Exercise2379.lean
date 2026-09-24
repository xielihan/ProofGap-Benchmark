import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise2379
noncomputable section

open Filter
open scoped Interval

def weight (x : ℝ) : ℝ := Real.sqrt x / (x + 100)
def cosineIntegrand (x : ℝ) : ℝ := weight x * Real.cos x
def doubleCosineIntegrand (x : ℝ) : ℝ := weight x * Real.cos (2 * x)
def squaredCosineIntegrand (x : ℝ) : ℝ := weight x * Real.cos x ^ 2
def absoluteCosineIntegrand (x : ℝ) : ℝ := weight x * |Real.cos x|

private theorem weight_nonneg (x : ℝ) : 0 ≤ weight x := by
  unfold weight
  by_cases hx : 0 ≤ x
  · exact div_nonneg (Real.sqrt_nonneg _) (by linarith)
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [Real.sqrt_eq_zero_of_nonpos hx']
    simp

private theorem rpow_half_eq_sqrt_of_pos (x : ℝ) (hx : 0 < x) :
    Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
  have hp : 0 ≤ Real.rpow x (1 / 2 : ℝ) :=
    Real.rpow_nonneg hx.le _
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hp2 : (Real.rpow x (1 / 2 : ℝ)) ^ 2 = x := by
    calc
      (Real.rpow x (1 / 2 : ℝ)) ^ 2 =
          Real.rpow x (1 / 2 : ℝ) * Real.rpow x (1 / 2 : ℝ) := by ring
      _ = Real.rpow x ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
        exact (Real.rpow_add hx (1 / 2 : ℝ) (1 / 2 : ℝ)).symm
      _ = x := by norm_num
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  nlinarith [sq_nonneg (Real.rpow x (1 / 2 : ℝ) - Real.sqrt x)]

private theorem scaled_weight_tendsto :
    Tendsto (fun x : ℝ => Real.rpow x (1 / 2 : ℝ) * weight x)
      atTop (nhds 1) := by
  have hden : Tendsto (fun x : ℝ => x + 100) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (b - 100)] with x hx
    linarith
  have hinv : Tendsto (fun x : ℝ => (x + 100)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hlim : Tendsto (fun x : ℝ => 1 - 100 * (x + 100)⁻¹)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  have heq :
      (fun x : ℝ => Real.rpow x (1 / 2 : ℝ) * weight x) =ᶠ[atTop]
        (fun x => 1 - 100 * (x + 100)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hd : x + 100 ≠ 0 := by linarith
    have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    calc
      Real.rpow x (1 / 2 : ℝ) * weight x = x / (x + 100) := by
        rw [rpow_half_eq_sqrt_of_pos x hx]
        unfold weight
        field_simp [hd]
        nlinarith
      _ = 1 - 100 * (x + 100)⁻¹ := by
        field_simp [hd]
        ring
  exact (tendsto_congr' heq).2 hlim

private theorem weight_continuousOn_nonneg :
    ContinuousOn weight (Set.Ici (0 : ℝ)) := by
  unfold weight
  exact Real.continuous_sqrt.continuousOn.div
    (continuous_id.continuousOn.add continuous_const.continuousOn)
    (fun x hx => by
      simp only [Set.mem_Ici] at hx
      linarith)

private theorem intervalIntegrable_weight (A : ℝ) (hA : 0 ≤ A) :
    IntervalIntegrable weight MeasureTheory.volume 0 A := by
  apply ContinuousOn.intervalIntegrable
  have hw : ContinuousOn weight (Set.Icc (0 : ℝ) A) :=
    weight_continuousOn_nonneg.mono (fun x hx => hx.1)
  simpa [Set.uIcc_of_le hA] using hw

private theorem intervalIntegrable_weight_between
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable weight MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hw : ContinuousOn weight (Set.Icc a b) :=
    weight_continuousOn_nonneg.mono (fun x hx => ha.trans hx.1)
  simpa [Set.uIcc_of_le hab] using hw

private theorem intervalIntegrable_doubleCosine (A : ℝ) (hA : 0 ≤ A) :
    IntervalIntegrable doubleCosineIntegrand MeasureTheory.volume 0 A := by
  apply ContinuousOn.intervalIntegrable
  have hw : ContinuousOn weight (Set.Icc (0 : ℝ) A) :=
    weight_continuousOn_nonneg.mono (fun x hx => hx.1)
  have hc : ContinuousOn (fun x : ℝ => Real.cos (2 * x)) (Set.Icc 0 A) :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousOn
  simpa [doubleCosineIntegrand, Set.uIcc_of_le hA] using hw.mul hc

private theorem intervalIntegrable_squaredCosine (A : ℝ) (hA : 0 ≤ A) :
    IntervalIntegrable squaredCosineIntegrand MeasureTheory.volume 0 A := by
  apply ContinuousOn.intervalIntegrable
  have hw : ContinuousOn weight (Set.Icc (0 : ℝ) A) :=
    weight_continuousOn_nonneg.mono (fun x hx => hx.1)
  have hc : ContinuousOn (fun x : ℝ => Real.cos x ^ 2) (Set.Icc 0 A) :=
    (Real.continuous_cos.pow 2).continuousOn
  simpa [squaredCosineIntegrand, Set.uIcc_of_le hA] using hw.mul hc

private theorem intervalIntegrable_absoluteCosine (A : ℝ) (hA : 0 ≤ A) :
    IntervalIntegrable absoluteCosineIntegrand MeasureTheory.volume 0 A := by
  apply ContinuousOn.intervalIntegrable
  have hw : ContinuousOn weight (Set.Icc (0 : ℝ) A) :=
    weight_continuousOn_nonneg.mono (fun x hx => hx.1)
  have hc : ContinuousOn (fun x : ℝ => |Real.cos x|) (Set.Icc 0 A) :=
    Real.continuous_cos.abs.continuousOn
  simpa [absoluteCosineIntegrand, Set.uIcc_of_le hA] using hw.mul hc

private theorem inv_two_sqrt_le_weight {x : ℝ} (hx : 100 ≤ x) :
    (2 * Real.sqrt x)⁻¹ ≤ weight x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hd : 0 < x + 100 := by linarith
  rw [inv_eq_one_div]
  unfold weight
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hs) hd).2
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  nlinarith

private theorem intervalIntegrable_inv_two_sqrt
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => (2 * Real.sqrt x)⁻¹)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hsqrt : ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc a b) :=
    Real.continuous_sqrt.continuousOn
  have hne : ∀ x ∈ Set.Icc a b, 2 * Real.sqrt x ≠ 0 := by
    intro x hx
    have : 0 < Real.sqrt x := Real.sqrt_pos.2 (ha.trans_le hx.1)
    positivity
  have hc : ContinuousOn (fun x : ℝ => (2 * Real.sqrt x)⁻¹) (Set.Icc a b) :=
    (continuous_const.continuousOn.mul hsqrt).inv₀ hne
  simpa [Set.uIcc_of_le hab] using hc

private def weightDerivative (x : ℝ) : ℝ :=
  (100 - x) / (2 * Real.sqrt x * (x + 100) ^ 2)

private theorem hasDerivAt_weight_of_pos (x : ℝ) (hx : 0 < x) :
    HasDerivAt weight (weightDerivative x) x := by
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hd : x + 100 ≠ 0 := by linarith
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  unfold weight weightDerivative
  convert
    (Real.hasDerivAt_sqrt (ne_of_gt hx)).div
      ((hasDerivAt_id x).add_const 100) hd using 1 <;>
    field_simp [hs, hd] <;>
    simp [hs2] <;>
    ring

private theorem weightDerivative_nonpos {x : ℝ} (hx : 100 ≤ x) :
    weightDerivative x ≤ 0 := by
  unfold weightDerivative
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
    (mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg x))
      (sq_nonneg (x + 100)))

private theorem weightDerivative_continuousOn
    (a b : ℝ) (ha : 0 < a) :
    ContinuousOn weightDerivative (Set.Icc a b) := by
  have hnum : Continuous (fun x : ℝ => 100 - x) :=
    continuous_const.sub continuous_id
  have hden : Continuous
      (fun x : ℝ => 2 * Real.sqrt x * (x + 100) ^ 2) :=
    (continuous_const.mul Real.continuous_sqrt).mul
      ((continuous_id.add continuous_const).pow 2)
  unfold weightDerivative
  exact hnum.continuousOn.div hden.continuousOn
    (fun x hx => by
      have hxpos : 0 < x := ha.trans_le hx.1
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
      have hd : 0 < x + 100 := by linarith
      positivity)

private theorem intervalIntegrable_weightDerivative
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable weightDerivative MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  simpa [Set.uIcc_of_le hab] using
    (weightDerivative_continuousOn a b ha)

private theorem intervalIntegrable_weight_cos
    (c a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => weight x * Real.cos (c * x))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hw : ContinuousOn weight (Set.Icc a b) :=
    weight_continuousOn_nonneg.mono (fun x hx => ha.trans hx.1)
  have hc : ContinuousOn (fun x : ℝ => Real.cos (c * x)) (Set.Icc a b) :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousOn
  simpa [Set.uIcc_of_le hab] using hw.mul hc

private theorem intervalIntegrable_weightDerivative_sin
    (c a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun x : ℝ => weightDerivative x * (Real.sin (c * x) / c))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hd := weightDerivative_continuousOn a b ha
  have hs : ContinuousOn (fun x : ℝ => Real.sin (c * x) / c)
      (Set.Icc a b) :=
    ((Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).div_const c).continuousOn
  simpa [Set.uIcc_of_le hab] using hd.mul hs

private theorem oscillatory_tail_bound
    (c a b : ℝ) (hc : 0 < c) (ha : 100 ≤ a) (hab : a ≤ b) :
    |∫ x in a..b, weight x * Real.cos (c * x)| ≤
      2 * weight a / c := by
  have hb : 100 ≤ b := ha.trans hab
  have hdInt : IntervalIntegrable weightDerivative MeasureTheory.volume a b :=
    intervalIntegrable_weightDerivative a b (by linarith) hab
  have hoInt :
      IntervalIntegrable (fun x : ℝ => weight x * Real.cos (c * x))
        MeasureTheory.volume a b :=
    intervalIntegrable_weight_cos c a b (by linarith) hab
  have hpInt :
      IntervalIntegrable
        (fun x : ℝ => weightDerivative x * (Real.sin (c * x) / c))
        MeasureTheory.volume a b :=
    intervalIntegrable_weightDerivative_sin c a b (by linarith) hab
  have hqInt :
      IntervalIntegrable (fun x : ℝ => -weightDerivative x / c)
        MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hq : ContinuousOn (fun x : ℝ => -weightDerivative x / c)
        (Set.Icc a b) :=
      (weightDerivative_continuousOn a b (by linarith)).neg.div_const c
    simpa [Set.uIcc_of_le hab] using hq
  have hdFTC :
      (∫ x in a..b, weightDerivative x) = weight b - weight a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_weight_of_pos x (by
        rw [Set.uIcc_of_le hab] at hx
        linarith [ha, hx.1])) hdInt
  have hsinDer (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.sin (c * y) / c)
        (Real.cos (c * x)) x := by
    convert
      (((Real.hasDerivAt_sin (c * x)).comp x
        ((hasDerivAt_id x).const_mul c)).div_const c) using 1 <;>
      field_simp [ne_of_gt hc] <;> ring
  have hprodDer : ∀ x ∈ Set.uIcc a b,
      HasDerivAt
        (fun y : ℝ => weight y * (Real.sin (c * y) / c))
        (weightDerivative x * (Real.sin (c * x) / c) +
          weight x * Real.cos (c * x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hasDerivAt_weight_of_pos x (by linarith [ha, hx.1])).mul
      (hsinDer x)
  have hprodFTC :
      (∫ x in a..b,
        weightDerivative x * (Real.sin (c * x) / c) +
          weight x * Real.cos (c * x)) =
        weight b * (Real.sin (c * b) / c) -
          weight a * (Real.sin (c * a) / c) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hprodDer
      (hpInt.add hoInt)
  have hformula :
      (∫ x in a..b, weight x * Real.cos (c * x)) =
        (weight b * (Real.sin (c * b) / c) -
          weight a * (Real.sin (c * a) / c)) -
          ∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c) := by
    rw [intervalIntegral.integral_add hpInt hoInt] at hprodFTC
    linarith
  have hpAbs : ∀ x ∈ Set.Icc a b,
      |weightDerivative x * (Real.sin (c * x) / c)| ≤
        -weightDerivative x / c := by
    intro x hx
    have hdx : weightDerivative x ≤ 0 :=
      weightDerivative_nonpos (ha.trans hx.1)
    calc
      |weightDerivative x * (Real.sin (c * x) / c)| =
          (-weightDerivative x) * (|Real.sin (c * x)| / c) := by
        rw [abs_mul, abs_div, abs_of_nonpos hdx, abs_of_pos hc]
      _ ≤ (-weightDerivative x) * (1 / c) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (Real.abs_sin_le_one (c * x)) hc.le)
          (neg_nonneg.mpr hdx)
      _ = -weightDerivative x / c := by ring
  have hpUpper :
      (∫ x in a..b, weightDerivative x * (Real.sin (c * x) / c)) ≤
        ∫ x in a..b, -weightDerivative x / c :=
    intervalIntegral.integral_mono_on hab hpInt hqInt
      (fun x hx => (abs_le.mp (hpAbs x hx)).2)
  have hpLowerRaw :
      (∫ x in a..b, -(-weightDerivative x / c)) ≤
        ∫ x in a..b,
          weightDerivative x * (Real.sin (c * x) / c) :=
    intervalIntegral.integral_mono_on hab hqInt.neg hpInt
      (fun x hx => (abs_le.mp (hpAbs x hx)).1)
  have hpLower :
      -(∫ x in a..b, -weightDerivative x / c) ≤
        ∫ x in a..b,
          weightDerivative x * (Real.sin (c * x) / c) := by
    simpa only [intervalIntegral.integral_neg] using hpLowerRaw
  have hqeq :
      (∫ x in a..b, -weightDerivative x / c) =
        (weight a - weight b) / c := by
    calc
      (∫ x in a..b, -weightDerivative x / c) =
          (-1 / c) * (∫ x in a..b, weightDerivative x) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = (weight a - weight b) / c := by
        rw [hdFTC]
        ring
  have hpBound :
      |∫ x in a..b,
        weightDerivative x * (Real.sin (c * x) / c)| ≤
        (weight a - weight b) / c := by
    apply abs_le.2
    constructor
    · rw [← hqeq]
      exact hpLower
    · rw [← hqeq]
      exact hpUpper
  have hwa : 0 ≤ weight a := weight_nonneg a
  have hwb : 0 ≤ weight b := weight_nonneg b
  have htermA :
      |weight a * (Real.sin (c * a) / c)| ≤ weight a / c := by
    calc
      |weight a * (Real.sin (c * a) / c)| =
          weight a * (|Real.sin (c * a)| / c) := by
        rw [abs_mul, abs_div, abs_of_nonneg hwa, abs_of_pos hc]
      _ ≤ weight a * (1 / c) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (Real.abs_sin_le_one (c * a)) hc.le) hwa
      _ = weight a / c := by ring
  have htermB :
      |weight b * (Real.sin (c * b) / c)| ≤ weight b / c := by
    calc
      |weight b * (Real.sin (c * b) / c)| =
          weight b * (|Real.sin (c * b)| / c) := by
        rw [abs_mul, abs_div, abs_of_nonneg hwb, abs_of_pos hc]
      _ ≤ weight b * (1 / c) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (Real.abs_sin_le_one (c * b)) hc.le) hwb
      _ = weight b / c := by ring
  have htri :
      |(weight b * (Real.sin (c * b) / c) -
          weight a * (Real.sin (c * a) / c)) -
          (∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c))| ≤
        |weight b * (Real.sin (c * b) / c)| +
          |weight a * (Real.sin (c * a) / c)| +
          |∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c)| := by
    calc
      |(weight b * (Real.sin (c * b) / c) -
          weight a * (Real.sin (c * a) / c)) -
          (∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c))| =
        |(weight b * (Real.sin (c * b) / c) +
          -(weight a * (Real.sin (c * a) / c))) +
          -(∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c))| := by
          ring
      _ ≤ |weight b * (Real.sin (c * b) / c) +
          -(weight a * (Real.sin (c * a) / c))| +
          |-(∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c))| :=
        abs_add_le _ _
      _ ≤ (|weight b * (Real.sin (c * b) / c)| +
          |-(weight a * (Real.sin (c * a) / c))|) +
          |-(∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c))| := by
        linarith [abs_add_le
          (weight b * (Real.sin (c * b) / c))
          (-(weight a * (Real.sin (c * a) / c)))]
      _ = |weight b * (Real.sin (c * b) / c)| +
          |weight a * (Real.sin (c * a) / c)| +
          |∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c)| := by
        simp only [abs_neg]
  calc
    |∫ x in a..b, weight x * Real.cos (c * x)| =
        |(weight b * (Real.sin (c * b) / c) -
          weight a * (Real.sin (c * a) / c)) -
          (∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c))| := by
      rw [hformula]
    _ ≤ |weight b * (Real.sin (c * b) / c)| +
          |weight a * (Real.sin (c * a) / c)| +
          |∫ x in a..b,
            weightDerivative x * (Real.sin (c * x) / c)| := htri
    _ ≤ weight b / c + weight a / c + (weight a - weight b) / c :=
      add_le_add (add_le_add htermB htermA) hpBound
    _ = 2 * weight a / c := by ring

private theorem oscillatory_integral_converges
    (c : ℝ) (hc : 0 < c) (hzero : Tendsto weight atTop (nhds 0)) :
    ∃ L : ℝ,
      Tendsto
        (fun A => ∫ x in (0 : ℝ)..A, weight x * Real.cos (c * x))
        atTop (nhds L) := by
  have hdiff : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ x in (0 : ℝ)..b, weight x * Real.cos (c * x)) -
          (∫ x in (0 : ℝ)..a, weight x * Real.cos (c * x)) =
        ∫ x in a..b, weight x * Real.cos (c * x) := by
    intro a b ha hab
    have h0a := intervalIntegrable_weight_cos c 0 a (by norm_num) ha
    have habInt := intervalIntegrable_weight_cos c a b ha hab
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals h0a habInt
    linarith
  have hcauchy :
      Cauchy (map
        (fun A => ∫ x in (0 : ℝ)..A, weight x * Real.cos (c * x))
        atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    have hdelta : 0 < ε * c / 2 := by positivity
    have hwsmall : ∀ᶠ x : ℝ in atTop, weight x < ε * c / 2 :=
      hzero.eventually (Iio_mem_nhds hdelta)
    let F : ℝ → ℝ :=
      fun A => ∫ x in (0 : ℝ)..A, weight x * Real.cos (c * x)
    let s : Set ℝ :=
      {A : ℝ | (100 : ℝ) ≤ A ∧ weight A < ε * c / 2}
    refine ⟨F '' s, ?_, ?_⟩
    · change F ⁻¹' (F '' s) ∈ atTop
      filter_upwards [eventually_ge_atTop (100 : ℝ), hwsmall] with A hA hAw
      exact ⟨A, ⟨hA, hAw⟩, rfl⟩
    · intro u hu v hv
      rcases hu with ⟨a, ha, rfl⟩
      rcases hv with ⟨b, hb, rfl⟩
      change (100 : ℝ) ≤ a ∧ weight a < ε * c / 2 at ha
      change (100 : ℝ) ≤ b ∧ weight b < ε * c / 2 at hb
      rcases ha with ⟨ha, hwa⟩
      rcases hb with ⟨hb, hwb⟩
      dsimp only [F]
      rw [Real.dist_eq]
      rcases le_total a b with hab | hba
      · have htail := oscillatory_tail_bound c a b hc ha hab
        have hlt : 2 * weight a / c < ε := by
          apply (div_lt_iff₀ hc).2
          linarith
        calc
          |(∫ x in (0 : ℝ)..a, weight x * Real.cos (c * x)) -
              (∫ x in (0 : ℝ)..b, weight x * Real.cos (c * x))| =
            |(∫ x in (0 : ℝ)..b, weight x * Real.cos (c * x)) -
              (∫ x in (0 : ℝ)..a, weight x * Real.cos (c * x))| :=
            abs_sub_comm _ _
          _ = |∫ x in a..b, weight x * Real.cos (c * x)| := by
            rw [hdiff a b (by linarith) hab]
          _ < ε := htail.trans_lt hlt
      · have htail := oscillatory_tail_bound c b a hc hb hba
        have hlt : 2 * weight b / c < ε := by
          apply (div_lt_iff₀ hc).2
          linarith
        calc
          |(∫ x in (0 : ℝ)..a, weight x * Real.cos (c * x)) -
              (∫ x in (0 : ℝ)..b, weight x * Real.cos (c * x))| =
            |∫ x in b..a, weight x * Real.cos (c * x)| := by
              rw [hdiff b a (by linarith) hba]
          _ < ε := htail.trans_lt hlt
  exact (cauchy_map_iff_exists_tendsto).1 hcauchy

theorem gap1 (A : ℝ) (hA : 0 < A) :
    |∫ x in (0 : ℝ)..A, Real.cos x| ≤ 2 := by
  have hcos :
      IntervalIntegrable Real.cos MeasureTheory.volume (0 : ℝ) A :=
    Real.continuous_cos.intervalIntegrable
      (μ := MeasureTheory.volume) 0 A
  have hi :
      (∫ x in (0 : ℝ)..A, Real.cos x) = Real.sin A - Real.sin 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sin x) hcos
  rw [hi, Real.sin_zero, sub_zero]
  exact (Real.abs_sin_le_one A).trans (by norm_num)

theorem gap2 :
    Tendsto weight atTop (nhds 0) := by
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop
  have hinv : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hprod := scaled_weight_tendsto.mul hinv
  have heq :
      (fun x : ℝ => weight x) =ᶠ[atTop]
        (fun x =>
          (Real.rpow x (1 / 2 : ℝ) * weight x) * (Real.sqrt x)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [rpow_half_eq_sqrt_of_pos x hx]
    have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
    field_simp [hs]
  apply (tendsto_congr' heq).2
  simpa using hprod

theorem gap3 :
    AntitoneOn weight (Set.Ici (100 : ℝ)) := by
  intro x hx y hy hxy
  have hx100 : (100 : ℝ) ≤ x := hx
  have hy100 : (100 : ℝ) ≤ y := hy
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hxd : 0 < x + 100 := by linarith
  have hyd : 0 < y + 100 := by linarith
  unfold weight
  apply (div_le_div_iff₀ hyd hxd).2
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hsy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0
  have hmul : (100 : ℝ) * 100 ≤ x * y :=
    mul_le_mul hx100 hy100 (by norm_num) hx0
  have hxy100 : 0 ≤ x * y - 10000 := by
    norm_num at hmul ⊢
    exact hmul
  have hfac : 0 ≤ (y - x) * (x * y - 10000) :=
    mul_nonneg (sub_nonneg.mpr hxy) hxy100
  have hsquares :
      (Real.sqrt y * (x + 100)) ^ 2 ≤
        (Real.sqrt x * (y + 100)) ^ 2 := by
    rw [mul_pow, mul_pow, hsx, hsy]
    nlinarith [hfac]
  have hl : 0 ≤ Real.sqrt y * (x + 100) :=
    mul_nonneg (Real.sqrt_nonneg _) hxd.le
  have hr : 0 ≤ Real.sqrt x * (y + 100) :=
    mul_nonneg (Real.sqrt_nonneg _) hyd.le
  nlinarith [sq_nonneg
    (Real.sqrt x * (y + 100) - Real.sqrt y * (x + 100))]

theorem gap4 :
    ∃ L : ℝ,
      Tendsto (fun A => ∫ x in (0 : ℝ)..A, cosineIntegrand x)
        atTop (nhds L) := by
  obtain ⟨L, hL⟩ :=
    oscillatory_integral_converges (1 : ℝ) (by norm_num) gap2
  refine ⟨L, ?_⟩
  simpa [cosineIntegrand] using hL

theorem gap5 (x : ℝ) :
    squaredCosineIntegrand x ≤ absoluteCosineIntegrand x := by
  have hw : 0 ≤ weight x := weight_nonneg x
  have hc : Real.cos x ^ 2 ≤ |Real.cos x| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (Real.cos x), Real.abs_cos_le_one x]
  unfold squaredCosineIntegrand absoluteCosineIntegrand
  exact mul_le_mul_of_nonneg_left hc hw

theorem gap6 (x : ℝ) :
    squaredCosineIntegrand x =
      (1 / 2 : ℝ) * (weight x + doubleCosineIntegrand x) := by
  unfold squaredCosineIntegrand doubleCosineIntegrand
  rw [Real.cos_two_mul]
  ring

theorem gap7 (x : ℝ) :
    (1 / 2 : ℝ) * (weight x + doubleCosineIntegrand x) ≤
      absoluteCosineIntegrand x := by
  rw [← gap6 x]
  exact gap5 x

theorem gap8 :
    Tendsto (fun x => Real.rpow x (1 / 2 : ℝ) * weight x)
      atTop (nhds 1) := by
  exact scaled_weight_tendsto

theorem gap9 :
    Tendsto (fun A => ∫ x in (0 : ℝ)..A, weight x) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hs : ∀ᶠ A : ℝ in atTop, b + 10 < Real.sqrt A :=
    Real.tendsto_sqrt_atTop (eventually_gt_atTop (b + 10))
  filter_upwards [hs, eventually_ge_atTop (100 : ℝ)] with A hsA hA
  have hw0 := intervalIntegrable_weight 100 (by norm_num)
  have hwTail := intervalIntegrable_weight_between 100 A (by norm_num) hA
  have hrootInt :
      (∫ x in (100 : ℝ)..A, (2 * Real.sqrt x)⁻¹) =
        Real.sqrt A - 10 := by
    have hder : ∀ x ∈ Set.uIcc (100 : ℝ) A,
        HasDerivAt Real.sqrt ((2 * Real.sqrt x)⁻¹) x := by
      intro x hx
      rw [Set.uIcc_of_le hA] at hx
      simpa [one_div] using
        (Real.hasDerivAt_sqrt (by linarith [hx.1] : x ≠ 0))
    have hint :=
      intervalIntegrable_inv_two_sqrt 100 A (by norm_num) hA
    have hi :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
    norm_num at hi
    calc
      (∫ x in (100 : ℝ)..A, (2 * Real.sqrt x)⁻¹) =
          ∫ x in (100 : ℝ)..A, (Real.sqrt x)⁻¹ * (1 / 2 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hA] at hx
        have hsx : Real.sqrt x ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 (by linarith [hx.1]))
        field_simp [hsx]
      _ = (∫ x in (100 : ℝ)..A, (Real.sqrt x)⁻¹) * (1 / 2 : ℝ) := by
        rw [intervalIntegral.integral_mul_const]
      _ = Real.sqrt A - 10 := hi
  have htail :
      Real.sqrt A - 10 ≤ ∫ x in (100 : ℝ)..A, weight x := by
    rw [← hrootInt]
    exact intervalIntegral.integral_mono_on hA
      (intervalIntegrable_inv_two_sqrt 100 A (by norm_num) hA)
      hwTail (fun x hx => inv_two_sqrt_le_weight hx.1)
  have hfirst : 0 ≤ ∫ x in (0 : ℝ)..(100 : ℝ), weight x :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ => weight_nonneg x)
  have hadd :
      (∫ x in (0 : ℝ)..(100 : ℝ), weight x) +
          (∫ x in (100 : ℝ)..A, weight x) =
        ∫ x in (0 : ℝ)..A, weight x :=
    intervalIntegral.integral_add_adjacent_intervals hw0 hwTail
  nlinarith

theorem gap10 :
    ∃ L : ℝ,
      Tendsto (fun A => ∫ x in (0 : ℝ)..A, doubleCosineIntegrand x)
        atTop (nhds L) := by
  obtain ⟨L, hL⟩ :=
    oscillatory_integral_converges (2 : ℝ) (by norm_num) gap2
  refine ⟨L, ?_⟩
  simpa [doubleCosineIntegrand] using hL

theorem gap11 :
    Tendsto (fun A => ∫ x in (0 : ℝ)..A, squaredCosineIntegrand x)
      atTop atTop := by
  obtain ⟨L, hL⟩ := gap10
  have hweightTop := gap9
  rw [tendsto_atTop] at hweightTop ⊢
  intro b
  have hdouble : ∀ᶠ A in atTop,
      L - 1 < ∫ x in (0 : ℝ)..A, doubleCosineIntegrand x :=
    (hL.eventually (Ioo_mem_nhds
      (by linarith : L - 1 < L) (by linarith : L < L + 1))).mono
      (fun A h => h.1)
  have hweight := hweightTop (2 * b - (L - 1))
  filter_upwards [hdouble, hweight, eventually_ge_atTop (0 : ℝ)] with A hD hW hA
  have hw := intervalIntegrable_weight A hA
  have hd := intervalIntegrable_doubleCosine A hA
  have heq :
      (∫ x in (0 : ℝ)..A, squaredCosineIntegrand x) =
        (1 / 2 : ℝ) *
          ((∫ x in (0 : ℝ)..A, weight x) +
            ∫ x in (0 : ℝ)..A, doubleCosineIntegrand x) := by
    calc
      (∫ x in (0 : ℝ)..A, squaredCosineIntegrand x) =
          ∫ x in (0 : ℝ)..A,
            (1 / 2 : ℝ) * (weight x + doubleCosineIntegrand x) :=
        intervalIntegral.integral_congr (fun x _ => gap6 x)
      _ = (1 / 2 : ℝ) *
          ((∫ x in (0 : ℝ)..A, weight x) +
            ∫ x in (0 : ℝ)..A, doubleCosineIntegrand x) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add hw hd]
  rw [heq]
  linarith

theorem gap12 :
    Tendsto (fun A => ∫ x in (0 : ℝ)..A, absoluteCosineIntegrand x)
      atTop atTop := by
  have hsquareTop := gap11
  rw [tendsto_atTop] at hsquareTop ⊢
  intro b
  have hsquare := hsquareTop b
  filter_upwards [hsquare, eventually_ge_atTop (0 : ℝ)] with A hb hA
  have hs := intervalIntegrable_squaredCosine A hA
  have ha := intervalIntegrable_absoluteCosine A hA
  exact hb.trans (intervalIntegral.integral_mono_on hA hs ha
    (fun x _ => gap5 x))

end
end ProofGap.Exercise2379
