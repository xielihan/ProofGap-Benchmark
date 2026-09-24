import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Central

namespace ProofGap.Exercise3016

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n

def term (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * coefficient n * x ^ n

def seriesFunction (x : ℝ) : ℝ := ∑' n : ℕ, term x n

private def positiveHalfChoose (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Ring.choose (-(1 / 2 : ℝ)) n

private theorem ringChoose_succ (r : ℝ) (n : ℕ) :
    Ring.choose r (n + 1) =
      Ring.choose r n * (r - n) / (n + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_natCast,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hn]
  ring

private theorem positiveHalfChoose_succ (n : ℕ) :
    positiveHalfChoose (n + 1) =
      positiveHalfChoose n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  rw [positiveHalfChoose, positiveHalfChoose, ringChoose_succ, pow_succ]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]
  ring

private theorem coefficient_succ (n : ℕ) :
    coefficient (n + 1) =
      coefficient n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  have hnat := Nat.succ_mul_centralBinom_succ n
  have hreal := congrArg (fun m : ℕ => (m : ℝ)) hnat
  simp only [Nat.centralBinom] at hreal
  push_cast at hreal
  rw [coefficient, coefficient, pow_succ]
  have hp : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hp, hn]
  nlinarith

private theorem positiveHalfChoose_eq_coefficient (n : ℕ) :
    positiveHalfChoose n = coefficient n := by
  induction n with
  | zero =>
      norm_num [positiveHalfChoose, coefficient,
        Ring.choose_zero_right, Nat.choose]
  | succ n ih =>
      rw [positiveHalfChoose_succ, coefficient_succ, ih]

private theorem coefficient_nonneg (n : ℕ) :
    0 ≤ coefficient n := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

private theorem harmonicLowerBound (n : ℕ) :
    1 / (2 * (((n + 1 : ℕ) : ℝ))) ≤ coefficient (n + 1) := by
  have hnat :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom (n + 1) (by omega)
  have hreal :
      (4 : ℝ) ^ (n + 1) ≤
        2 * ((n + 1 : ℕ) : ℝ) * (Nat.centralBinom (n + 1) : ℝ) := by
    exact_mod_cast hnat
  simp only [Nat.centralBinom] at hreal
  rw [coefficient]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

private theorem coefficient_not_summable :
    ¬ Summable coefficient := by
  intro hcoeff
  have hshift : Summable (fun n : ℕ => coefficient (n + 1)) :=
    (summable_nat_add_iff 1).2 hcoeff
  have hlower :
      Summable (fun n : ℕ => 1 / (2 * (((n + 1 : ℕ) : ℝ)))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) harmonicLowerBound hshift
  have hharmonicShift :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    convert hlower.mul_left 2 using 1
    funext n
    field_simp
  exact Real.not_summable_one_div_natCast <|
    (summable_nat_add_iff 1).1 <| by
      simpa [Nat.cast_add] using hharmonicShift

private theorem endpoint_not_summable :
    ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n * coefficient n) := by
  intro h
  apply coefficient_not_summable
  have hnorm := h.norm
  convert hnorm using 1
  funext n
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (coefficient_nonneg n)]
  simp

private theorem endpoint_tsum_eq_zero :
    (∑' n : ℕ, (-1 : ℝ) ^ n * coefficient n) = 0 := by
  exact tsum_eq_zero_of_not_summable endpoint_not_summable

theorem gap1 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Summable (term x) := by
  have hxabs : |x| < 1 := abs_lt.2 hx
  have hz : x ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, Real.dist_eq,
      ENNReal.ofReal_lt_one, sub_zero]
    exact hxabs
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := -(1 / 2 : ℝ))).hasSum hz
  have hfun :
      (fun n : ℕ =>
        (binomialSeries ℝ (-(1 / 2 : ℝ)) n) (fun _ => x)) =
        term x := by
    funext n
    rw [binomialSeries_apply]
    simp only [smul_eq_mul]
    rw [show (List.ofFn (fun _ : Fin n => x)).prod = x ^ n by simp]
    rw [term, ← positiveHalfChoose_eq_coefficient]
    simp [term, positiveHalfChoose, ← mul_assoc, ← mul_pow]
  rw [hfun] at h
  exact h.summable

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    seriesFunction x = 1 / Real.sqrt (1 + x) := by
  have hz : x ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, Real.dist_eq,
      ENNReal.ofReal_lt_one, sub_zero]
    exact hx
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := -(1 / 2 : ℝ))).hasSum hz
  have hfun :
      (fun n : ℕ =>
        (binomialSeries ℝ (-(1 / 2 : ℝ)) n) (fun _ => x)) =
        term x := by
    funext n
    rw [binomialSeries_apply]
    simp only [smul_eq_mul]
    rw [show (List.ofFn (fun _ : Fin n => x)).prod = x ^ n by simp]
    rw [term, ← positiveHalfChoose_eq_coefficient]
    simp [term, positiveHalfChoose, ← mul_assoc, ← mul_pow]
  rw [hfun] at h
  have hpos : 0 < 1 + x := by
    rw [abs_lt] at hx
    linarith
  have hvalue :
      (1 + x) ^ (-(1 / 2 : ℝ)) =
        1 / Real.sqrt (1 + x) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hpos.le]
    simp [one_div]
  rw [seriesFunction, h.tsum_eq]
  simpa only [zero_add] using hvalue

theorem gap3 :
    Tendsto seriesFunction (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (1 / Real.sqrt 2)) := by
  have harg :
      Tendsto (fun x : ℝ => 1 + x) (nhds (1 : ℝ)) (nhds (2 : ℝ)) := by
    convert
      (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun x : ℝ => 1 + x) 1).tendsto using 1 <;>
      norm_num [Pi.add_apply]
  have hsqrt :
      Tendsto (fun x : ℝ => Real.sqrt (1 + x))
        (nhds (1 : ℝ)) (nhds (Real.sqrt 2)) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp harg
  have hlimit :
      Tendsto (fun x : ℝ => 1 / Real.sqrt (1 + x))
        (nhdsWithin 1 (Set.Iio 1)) (𝓝 (1 / Real.sqrt 2)) :=
    (tendsto_const_nhds.div hsqrt (by positivity)).mono_left inf_le_left
  apply hlimit.congr'
  have hleft :
      ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), -1 < x :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  filter_upwards [hleft, self_mem_nhdsWithin] with x hxleft hxright
  exact (gap2 x (abs_lt.2 ⟨hxleft, hxright⟩)).symm

theorem gap4 :
    Tendsto (fun x : ℝ => 1 / Real.sqrt (1 + x))
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (1 / Real.sqrt 2)) := by
  have harg :
      Tendsto (fun x : ℝ => 1 + x) (nhds (1 : ℝ)) (nhds (2 : ℝ)) := by
    convert
      (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun x : ℝ => 1 + x) 1).tendsto using 1 <;>
      norm_num [Pi.add_apply]
  have hsqrt :
      Tendsto (fun x : ℝ => Real.sqrt (1 + x))
        (nhds (1 : ℝ)) (nhds (Real.sqrt 2)) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp harg
  exact (tendsto_const_nhds.div hsqrt (by positivity)).mono_left inf_le_left

private theorem actual_endpoint_limit :
    Tendsto seriesFunction (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (1 / Real.sqrt 2)) := by
  apply gap4.congr'
  have hleft :
      ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), -1 < x :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  filter_upwards [hleft, self_mem_nhdsWithin] with x hxleft hxright
  exact (gap2 x (abs_lt.2 ⟨hxleft, hxright⟩)).symm

private theorem gap1_statement_false :
    ¬ ∀ (x : ℝ), x ∈ Set.Ioc (-1 : ℝ) 1 → Summable (term x) := by
  intro h
  apply endpoint_not_summable
  convert h 1 (by constructor <;> norm_num) using 1
  funext n
  simp [term]

private theorem gap3_statement_false :
    ¬ Tendsto seriesFunction (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n * coefficient n)) := by
  intro h
  rw [endpoint_tsum_eq_zero] at h
  have hzero : (0 : ℝ) = 1 / Real.sqrt 2 :=
    tendsto_nhds_unique h actual_endpoint_limit
  have hpos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  linarith

private theorem gap5_statement_false :
    ¬ ((∑' n : ℕ, (-1 : ℝ) ^ n * coefficient n) =
        1 / Real.sqrt 2) := by
  rw [endpoint_tsum_eq_zero]
  positivity

private theorem coefficient_antitone : Antitone coefficient := by
  apply antitone_nat_of_succ_le
  intro n
  rw [coefficient_succ]
  have hc := coefficient_nonneg n
  have hratio :
      (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  calc
    coefficient n * (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1)) =
        coefficient n *
          ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) := by ring
    _ ≤ coefficient n := mul_le_of_le_one_right hc hratio

private theorem coefficient_sq_le (n : ℕ) :
    coefficient n ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num [coefficient, Nat.choose]
  | succ n ih =>
      rw [coefficient_succ]
      calc
        (coefficient n * (2 * (n : ℝ) + 1) /
              (2 * ((n : ℝ) + 1))) ^ 2 =
            coefficient n ^ 2 *
              ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) ^ 2 := by
                ring
        _ ≤ (1 / ((n : ℝ) + 1)) *
              ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) ^ 2 := by
                exact mul_le_mul_of_nonneg_right ih (sq_nonneg _)
        _ ≤ 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
                push_cast
                field_simp
                nlinarith

private theorem coefficient_tendsto_zero :
    Tendsto coefficient atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => coefficient n ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg (coefficient n)) coefficient_sq_le
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  convert hsqrt using 1
  · funext n
    exact (Real.sqrt_sq (coefficient_nonneg n)).symm
  · norm_num

theorem gap5 :
    ProofGap.SeriesHasSum
      (fun n : ℕ => (-1 : ℝ) ^ n * coefficient n)
      (1 / Real.sqrt 2) := by
  obtain ⟨l, hl⟩ :=
    coefficient_antitone.tendsto_alternating_series_of_tendsto_zero
      coefficient_tendsto_zero
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hfun :
      (fun x : ℝ =>
        ∑' n : ℕ, ((-1 : ℝ) ^ n * coefficient n) * x ^ n) =
        seriesFunction := by
    funext x
    apply tsum_congr
    intro n
    simp only [term, mul_assoc]
  rw [hfun] at hab
  have hlvalue : l = 1 / Real.sqrt 2 :=
    tendsto_nhds_unique hab gap3
  rw [hlvalue] at hl
  rw [ProofGap.SeriesHasSum, HasSum,
    SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  simpa only [Function.comp_apply] using hl

end

end ProofGap.Exercise3016
