import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2932_5

noncomputable section

open scoped BigOperators

def integrand (x : ℝ) : ℝ :=
  1 / (1 + x ^ 3)

def geometricTerm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (1 / x : ℝ) ^ (3 * n + 3)

def improperIntegral : ℝ :=
  ∫ x in Set.Ioi (2 : ℝ), integrand x

def powerIntegral (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (2 : ℝ), (1 / x : ℝ) ^ (3 * n + 3)

def integratedSeriesTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (3 * n + 2 : ℕ) *
    (1 / 2 : ℝ) ^ (3 * n + 2)

def seriesValue : ℝ :=
  ∑' n : ℕ, integratedSeriesTerm n

def θ : ℝ :=
  improperIntegral - (119 / 1000 : ℝ)

def partialFraction (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) * (1 / (1 + x)) -
    (1 / 3 : ℝ) * ((x - 2) / (x ^ 2 - x + 1))

def antiderivative (x : ℝ) : ℝ :=
  (1 / 6 : ℝ) *
      Real.log (((x + 1) ^ 2) / (x ^ 2 - x + 1)) +
    (1 / Real.sqrt 3) *
      Real.arctan ((2 * x - 1) / Real.sqrt 3)

def atInfinity : ℝ :=
  (1 / Real.sqrt 3) * (Real.pi / 2)

def closedForm : ℝ :=
  (Real.sqrt 3 / 3) * (Real.pi / 6) -
    (1 / 6 : ℝ) * Real.log 3

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem hasSum_geometricTerm {x : ℝ} (hx : 2 ≤ x) :
    HasSum (fun n => geometricTerm n x) (integrand x) := by
  have hx0 : x ≠ 0 := by linarith
  have hr : |-(1 / x : ℝ) ^ 3| < 1 := by
    rw [abs_neg, abs_pow, abs_div, abs_one, abs_of_nonneg (by linarith : 0 ≤ x)]
    have : (1 : ℝ) < x := by linarith
    simp only [one_div]
    exact pow_lt_one₀ (inv_nonneg.mpr (by linarith))
      (inv_lt_one_of_one_lt₀ this) (by norm_num)
  have h := (hasSum_geometric_of_abs_lt_one hr).mul_left ((1 / x : ℝ) ^ 3)
  convert h using 1
  · ext n
    simp only [geometricTerm]
    rw [neg_pow]
    ring
  · simp only [integrand]
    have hden : 1 + x ^ 3 ≠ 0 := by positivity
    have hinvden : 1 + (1 / x : ℝ) ^ 3 ≠ 0 := by positivity
    field_simp [hx0, hden, hinvden]
    rw [show x ^ 3 - -1 = 1 + x ^ 3 by ring, div_self hden]

private theorem powerIntegral_eq (n : ℕ) :
    powerIntegral n = 1 / (3 * n + 2 : ℕ) * (1 / 2 : ℝ) ^ (3 * n + 2) := by
  have hpow := integral_Ioi_rpow_of_lt
    (a := -((3 * n + 3 : ℕ) : ℝ)) (c := (2 : ℝ))
    (by push_cast; linarith) (by norm_num)
  rw [powerIntegral]
  convert hpow using 1
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx
    change (1 / x : ℝ) ^ (3 * n + 3) =
      x ^ (-((3 * n + 3 : ℕ) : ℝ))
    rw [Real.rpow_neg_natCast x (3 * n + 3), zpow_neg, zpow_natCast]
    simp only [one_div, inv_pow]
  · push_cast
    have hexp : -(3 * (n : ℝ) + 3) + 1 =
        -((3 * n + 2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hexp, Real.rpow_neg_natCast 2 (3 * n + 2), zpow_neg, zpow_natCast]
    simp only [one_div, inv_pow]
    have hk : (3 * (n : ℝ) + 2) ≠ 0 := by positivity
    have hp : (2 : ℝ) ^ (3 * n + 2) ≠ 0 := by positivity
    field_simp [hk, hp]
    push_cast <;> ring

private theorem hasSum_innerGeometric {x : ℝ} (hx : 2 ≤ x) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (1 / x : ℝ) ^ (3 * n))
      (1 / (1 + (1 / x : ℝ) ^ 3)) := by
  have hr : |-(1 / x : ℝ) ^ 3| < 1 := by
    rw [abs_neg, abs_pow, abs_div, abs_one, abs_of_nonneg (by linarith : 0 ≤ x)]
    have hx1 : (1 : ℝ) < x := by linarith
    simp only [one_div]
    exact pow_lt_one₀ (inv_nonneg.mpr (by linarith))
      (inv_lt_one_of_one_lt₀ hx1) (by norm_num)
  have h := hasSum_geometric_of_abs_lt_one hr
  convert h using 1
  · ext n
    rw [neg_pow]
    ring
  · ring

private theorem integrableOn_powerTerm (n : ℕ) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => (1 / x : ℝ) ^ (3 * n + 3)) (Set.Ioi (2 : ℝ)) := by
  have h := integrableOn_Ioi_rpow_of_lt
    (a := -((3 * n + 3 : ℕ) : ℝ)) (c := (2 : ℝ))
    (by push_cast; linarith) (by norm_num)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  change x ^ (-((3 * n + 3 : ℕ) : ℝ)) =
    (1 / x : ℝ) ^ (3 * n + 3)
  rw [Real.rpow_neg_natCast x (3 * n + 3), zpow_neg, zpow_natCast]
  simp only [one_div, inv_pow]

private theorem integrableOn_geometricTerm (n : ℕ) :
    MeasureTheory.IntegrableOn (geometricTerm n) (Set.Ioi (2 : ℝ)) := by
  have h := (integrableOn_powerTerm n).const_mul ((-1 : ℝ) ^ n)
  simpa only [geometricTerm] using h

private theorem normIntegral_geometricTerm (n : ℕ) :
    (∫ x in Set.Ioi (2 : ℝ), ‖geometricTerm n x‖) = powerIntegral n := by
  rw [powerIntegral]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  simp [geometricTerm, Real.norm_eq_abs, abs_of_pos hx0, one_div]

private theorem integral_geometricTerm (n : ℕ) :
    (∫ x in Set.Ioi (2 : ℝ), geometricTerm n x) =
      (-1 : ℝ) ^ n * powerIntegral n := by
  rw [powerIntegral]
  simp only [geometricTerm]
  rw [MeasureTheory.integral_const_mul]

private theorem summable_powerIntegral : Summable powerIntegral := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply hgeom.of_nonneg_of_le
  · intro n
    rw [powerIntegral_eq]
    positivity
  · intro n
    rw [powerIntegral_eq]
    calc
      1 / (3 * n + 2 : ℕ) * (1 / 2 : ℝ) ^ (3 * n + 2) ≤
          1 * (1 / 2 : ℝ) ^ (3 * n + 2) := by
        gcongr
        rw [one_div]
        apply (inv_le_one₀ (by positivity)).2
        push_cast
        have hn : (0 : ℝ) ≤ n := by positivity
        linarith
      _ = (1 / 2 : ℝ) ^ (3 * n + 2) := one_mul _
      _ ≤ (1 / 2 : ℝ) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

private theorem powerIntegral_nonneg (n : ℕ) : 0 ≤ powerIntegral n := by
  rw [powerIntegral_eq]
  positivity

private theorem improperIntegral_eq_integratedPowerSeries :
    improperIntegral = ∑' n : ℕ, (-1 : ℝ) ^ n * powerIntegral n := by
  have hFint : ∀ n : ℕ, MeasureTheory.Integrable (geometricTerm n)
      (MeasureTheory.volume.restrict (Set.Ioi (2 : ℝ))) := by
    intro n
    exact integrableOn_geometricTerm n
  have hnormsum : Summable (fun n : ℕ =>
      ∫ x, ‖geometricTerm n x‖ ∂(MeasureTheory.volume.restrict (Set.Ioi (2 : ℝ)))) := by
    change Summable (fun n : ℕ =>
      ∫ x in Set.Ioi (2 : ℝ), ‖geometricTerm n x‖)
    simpa only [normIntegral_geometricTerm] using summable_powerIntegral
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hnormsum
  calc
    improperIntegral = ∫ x in Set.Ioi (2 : ℝ), ∑' n : ℕ, geometricTerm n x := by
      rw [improperIntegral]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (hasSum_geometricTerm hx.le).tsum_eq.symm
    _ = ∑' n : ℕ, ∫ x in Set.Ioi (2 : ℝ), geometricTerm n x := by
      exact h.tsum_eq.symm
    _ = ∑' n : ℕ, (-1 : ℝ) ^ n * powerIntegral n := by
      apply tsum_congr
      exact integral_geometricTerm

private theorem antitone_powerIntegral : Antitone powerIntegral := by
  apply antitone_nat_of_succ_le
  intro n
  rw [powerIntegral_eq, powerIntegral_eq]
  apply mul_le_mul
  · apply one_div_le_one_div_of_le
    · positivity
    · push_cast
      linarith
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  · positivity
  · positivity

private theorem hasSum_integratedPowerSeries :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * powerIntegral n) improperIntegral := by
  rw [improperIntegral_eq_integratedPowerSeries]
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ n * powerIntegral n) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      Real.norm_eq_abs, abs_of_nonneg (powerIntegral_nonneg _), one_mul] using
      summable_powerIntegral
  exact hs.hasSum

private theorem tendsto_integratedPowerPartial :
    Tendsto (fun m => ∑ n ∈ Finset.range m,
      (-1 : ℝ) ^ n * powerIntegral n) atTop (nhds improperIntegral) :=
  hasSum_integratedPowerSeries.tendsto_sum_nat

private theorem improperIntegral_gt_119 :
    (119 / 1000 : ℝ) < improperIntegral := by
  have hlo := antitone_powerIntegral.alternating_series_le_tendsto
    tendsto_integratedPowerPartial 2
  norm_num [powerIntegral_eq, Finset.sum_range_succ] at hlo ⊢
  linarith

private theorem improperIntegral_lt_120 :
    improperIntegral < (120 / 1000 : ℝ) := by
  have hhi := antitone_powerIntegral.tendsto_le_alternating_series
    tendsto_integratedPowerPartial 1
  norm_num [powerIntegral_eq, Finset.sum_range_succ] at hhi ⊢
  linarith

private theorem theta_pos : 0 < θ := by
  rw [θ]
  exact sub_pos.mpr improperIntegral_gt_119

private theorem theta_lt : θ < (1 / 1000 : ℝ) := by
  rw [θ]
  have h := improperIntegral_lt_120
  norm_num at h ⊢
  linarith

private theorem integrand_eq_partialFraction {x : ℝ} (hx : 2 ≤ x) :
    integrand x = partialFraction x := by
  have hx1 : 1 + x ≠ 0 := by linarith
  have hq : x ^ 2 - x + 1 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  have hq' : 1 - x + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  have hq2 : x * (x - 1) + 1 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  have hc : 1 + x ^ 3 ≠ 0 := by positivity
  simp only [integrand, partialFraction]
  field_simp [hx1, hq, hc]
  ring

private theorem integrableOn_integrand :
    MeasureTheory.IntegrableOn integrand (Set.Ioi (2 : ℝ)) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable integrand
      (MeasureTheory.volume.restrict (Set.Ioi (2 : ℝ))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hden : 1 + x ^ 3 ≠ 0 := by
      have : 0 < x := lt_trans (by norm_num) hx
      positivity
    simpa only [integrand] using
      (continuousAt_const.div (continuousAt_const.add (continuousAt_id.pow 3)) hden).continuousWithinAt
  refine (integrableOn_powerTerm 0).mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hden : 0 < 1 + x ^ 3 := by positivity
  have hxpow : 0 < x ^ 3 := by positivity
  simp only [integrand, Real.norm_eq_abs]
  rw [abs_of_pos (one_div_pos.mpr hden)]
  rw [show (1 / x : ℝ) ^ 3 = 1 / x ^ 3 by ring]
  exact one_div_le_one_div_of_le hxpow (by linarith)

private theorem hasDerivAt_antiderivative {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt antiderivative (integrand x) x := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsne : Real.sqrt 3 ≠ 0 := hspos.ne'
  have hsquare : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hx1 : x + 1 ≠ 0 := by linarith
  have hq : x ^ 2 - x + 1 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  have hq' : x * (x - 1) + 1 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hnum := (hid.add_const 1).pow 2
  have hden := ((hid.pow 2).sub hid).add_const 1
  have hratio := hnum.div hden hq
  have hratio_ne : (x + 1) ^ 2 / (x ^ 2 - x + 1) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hx1) hq
  have hlog := (Real.hasDerivAt_log hratio_ne).comp x hratio
  have hlinear : HasDerivAt (fun y : ℝ => (2 * y - 1) / Real.sqrt 3)
      (2 / Real.sqrt 3) x := by
    convert ((hid.const_mul 2).sub_const 1).div_const (Real.sqrt 3) using 1 <;> ring
  have hatan := (Real.hasDerivAt_arctan ((2 * x - 1) / Real.sqrt 3)).comp x hlinear
  have h := hlog.const_mul (1 / 6 : ℝ) |>.add
    (hatan.const_mul (1 / Real.sqrt 3 : ℝ))
  convert h using 1
  simp only [integrand, Function.comp_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply,
    Pi.div_apply]
  norm_num
  field_simp [hx1, hq, hq', hsne]
  field_simp [hq']
  rw [hsquare]
  ring

private theorem tendsto_logRatio_atTop :
    Tendsto (fun x : ℝ =>
      Real.log (((x + 1) ^ 2) / (x ^ 2 - x + 1))) atTop (nhds 0) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hn : Tendsto (fun x : ℝ => (1 + x⁻¹) ^ 2) atTop (nhds 1) := by
    convert (tendsto_const_nhds.add hi).pow 2 using 1 <;> norm_num
  have hd : Tendsto (fun x : ℝ => 1 - x⁻¹ + (x⁻¹) ^ 2) atTop (nhds 1) := by
    convert (tendsto_const_nhds.sub hi).add (hi.pow 2) using 1 <;> norm_num
  have hnormalized : Tendsto (fun x : ℝ =>
      (1 + x⁻¹) ^ 2 / (1 - x⁻¹ + (x⁻¹) ^ 2)) atTop (nhds 1) := by
    convert hn.div hd (by norm_num) using 1 <;> norm_num
  have heq : (fun x : ℝ => ((x + 1) ^ 2) / (x ^ 2 - x + 1)) =ᶠ[atTop]
      (fun x : ℝ => (1 + x⁻¹) ^ 2 / (1 - x⁻¹ + (x⁻¹) ^ 2)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hq : x ^ 2 - x + 1 ≠ 0 := by
      nlinarith [sq_nonneg (2 * x - 1)]
    have hn : 1 - x⁻¹ + (x⁻¹) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (2 * x⁻¹ - 1)]
    field_simp [hx.ne', hq, hn]
  have hratio : Tendsto (fun x : ℝ => ((x + 1) ^ 2) / (x ^ 2 - x + 1))
      atTop (nhds 1) := hnormalized.congr' heq.symm
  simpa using (Real.continuousAt_log one_ne_zero).tendsto.comp hratio

private theorem tendsto_arctanPart_atTop :
    Tendsto (fun x : ℝ => Real.arctan ((2 * x - 1) / Real.sqrt 3))
      atTop (nhds (Real.pi / 2)) := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have harg : Tendsto (fun x : ℝ => (2 * x - 1) / Real.sqrt 3) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop ((b * Real.sqrt 3 + 1) / 2)] with x hx
    rw [le_div_iff₀ hspos]
    linarith
  exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg

private theorem tendsto_antiderivative_atTop :
    Tendsto antiderivative atTop (nhds atInfinity) := by
  have h := tendsto_logRatio_atTop.const_mul (1 / 6 : ℝ) |>.add
    (tendsto_arctanPart_atTop.const_mul (1 / Real.sqrt 3 : ℝ))
  change Tendsto (fun x : ℝ =>
    (1 / 6 : ℝ) * Real.log (((x + 1) ^ 2) / (x ^ 2 - x + 1)) +
      (1 / Real.sqrt 3) * Real.arctan ((2 * x - 1) / Real.sqrt 3))
    atTop (nhds atInfinity)
  simpa only [atInfinity, mul_zero, zero_add] using h

private theorem improperIntegral_eq_antiderivativeLimit :
    improperIntegral = atInfinity - antiderivative 2 := by
  rw [improperIntegral]
  exact MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x hx => hasDerivAt_antiderivative hx)
    integrableOn_integrand tendsto_antiderivative_atTop

private theorem improperIntegral_eq_partialFractionIntegral :
    improperIntegral = ∫ x in Set.Ioi (2 : ℝ), partialFraction x := by
  rw [improperIntegral]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact integrand_eq_partialFraction hx.le

private theorem antiderivative_two :
    antiderivative 2 = (1 / 6 : ℝ) * Real.log 3 +
      (1 / Real.sqrt 3) * (Real.pi / 3) := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsne : Real.sqrt 3 ≠ 0 := hspos.ne'
  have hsquare : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [antiderivative]
  norm_num

private theorem improperIntegral_closedExpansion :
    improperIntegral =
      (1 / Real.sqrt 3) * (Real.pi / 2) -
        (1 / 6 : ℝ) * Real.log 3 -
        (1 / Real.sqrt 3) * (Real.pi / 3) := by
  rw [improperIntegral_eq_antiderivativeLimit, atInfinity, antiderivative_two]
  ring

private theorem closedExpansion_eq_closedForm :
    (1 / Real.sqrt 3) * (Real.pi / 2) -
          (1 / 6 : ℝ) * Real.log 3 -
          (1 / Real.sqrt 3) * (Real.pi / 3) =
      closedForm := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsne : Real.sqrt 3 ≠ 0 := hspos.ne'
  have hsquare : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hinv : 1 / Real.sqrt 3 = Real.sqrt 3 / 3 := by
    field_simp [hsne]
    nlinarith
  rw [hinv]
  simp only [closedForm]
  ring

private theorem improperIntegral_eq_closedForm : improperIntegral = closedForm :=
  improperIntegral_closedExpansion.trans closedExpansion_eq_closedForm

private theorem approx_improperIntegral :
    Approx improperIntegral (119 / 1000 : ℝ) (1 / 1000 : ℝ) := by
  change |θ| < (1 / 1000 : ℝ)
  rw [abs_of_pos theta_pos]
  exact theta_lt

theorem gap1 :
    ∀ x : ℝ, 2 ≤ x →
      integrand x =
        (1 / x ^ 3) * (1 / (1 + (1 / x : ℝ) ^ 3)) := by
  intro x hx
  have hx0 : x ≠ 0 := by linarith
  simp only [integrand]
  field_simp [hx0]
  ring

theorem gap2 :
    ∀ x : ℝ, 2 ≤ x →
      (1 / x ^ 3) * (1 / (1 + (1 / x : ℝ) ^ 3)) =
        (1 / x : ℝ) ^ 3 *
          ∑' n : ℕ, (-1 : ℝ) ^ n * (1 / x : ℝ) ^ (3 * n) := by
  intro x hx
  rw [(hasSum_innerGeometric hx).tsum_eq]
  have hx0 : x ≠ 0 := by linarith
  field_simp [hx0]

theorem gap3 :
    ∀ x : ℝ, 2 ≤ x →
      (1 / x : ℝ) ^ 3 *
          (∑' n : ℕ, (-1 : ℝ) ^ n * (1 / x : ℝ) ^ (3 * n)) =
        ∑' n : ℕ, geometricTerm n x := by
  intro x hx
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [geometricTerm]
  ring

theorem gap4 :
    ∀ x : ℝ, 2 ≤ x →
      integrand x = ∑' n : ℕ, geometricTerm n x := by
  intro x hx
  exact (hasSum_geometricTerm hx).tsum_eq.symm

theorem gap5 :
    ∃ I : ℝ, I = improperIntegral := by
  exact ⟨improperIntegral, rfl⟩

theorem gap6 :
    improperIntegral =
      ∑' n : ℕ, (-1 : ℝ) ^ n * powerIntegral n := by
  exact improperIntegral_eq_integratedPowerSeries

theorem gap7 :
    (∑' n : ℕ, (-1 : ℝ) ^ n * powerIntegral n) =
      ∑' n : ℕ, integratedSeriesTerm n := by
  apply tsum_congr
  intro n
  rw [powerIntegral_eq]
  simp only [integratedSeriesTerm]
  push_cast
  ring

theorem gap8 :
    ∃ I : ℝ, I = seriesValue := by
  exact ⟨seriesValue, rfl⟩

theorem gap9 :
    ∃ I : ℝ, I = ∑' n : ℕ, integratedSeriesTerm n := by
  exact ⟨∑' n : ℕ, integratedSeriesTerm n, rfl⟩

theorem gap10 :
    improperIntegral = (119 / 1000 : ℝ) + θ := by
  simp only [θ]
  ring

theorem gap11 :
    0 < θ := by
  exact theta_pos

theorem gap12 :
    θ < (1 / 1000 : ℝ) := by
  exact theta_lt

theorem gap13 :
    improperIntegral =
      ∫ x in Set.Ioi (2 : ℝ), partialFraction x := by
  exact improperIntegral_eq_partialFractionIntegral

theorem gap14 :
    improperIntegral = atInfinity - antiderivative 2 := by
  exact improperIntegral_eq_antiderivativeLimit

theorem gap15 :
    improperIntegral =
      (1 / Real.sqrt 3) * (Real.pi / 2) -
        (1 / 6 : ℝ) * Real.log 3 -
        (1 / Real.sqrt 3) * (Real.pi / 3) := by
  exact improperIntegral_closedExpansion

theorem gap16 :
    (1 / Real.sqrt 3) * (Real.pi / 2) -
          (1 / 6 : ℝ) * Real.log 3 -
          (1 / Real.sqrt 3) * (Real.pi / 3) =
      closedForm := by
  exact closedExpansion_eq_closedForm

theorem gap17 :
    Approx closedForm (119 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  rw [← improperIntegral_eq_closedForm]
  exact approx_improperIntegral

theorem gap18 :
    Approx improperIntegral (119 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  exact approx_improperIntegral

end

end ProofGap.Exercise2932_5
