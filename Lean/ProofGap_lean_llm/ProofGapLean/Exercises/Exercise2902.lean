import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2902

noncomputable section

open scoped BigOperators Interval

def oddDoubleFactorial (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * k + 1 : ℕ)

def evenDoubleFactorial (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * (k + 1) : ℕ)

def binomialCoefficient (n : ℕ) : ℝ :=
  oddDoubleFactorial n / evenDoubleFactorial n

def integrandSeriesTerm (t : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  binomialCoefficient n * t ^ (4 * n)

def integratedSeriesTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  binomialCoefficient n * x ^ (4 * n + 1) / (4 * n + 1 : ℝ)

private theorem evenDoubleFactorial_eq (n : ℕ) :
    evenDoubleFactorial n =
      (2 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
  induction n with
  | zero =>
      norm_num [evenDoubleFactorial]
  | succ n ih =>
      simp only [evenDoubleFactorial, Finset.prod_range_succ]
      change
        evenDoubleFactorial n * ((2 * (n + 1) : ℕ) : ℝ) =
          (2 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ)
      rw [ih, pow_succ, Nat.factorial_succ]
      push_cast
      ring

private theorem descProd_neg_half (n : ℕ) :
    (∏ j ∈ Finset.range n, ((-1 / 2 : ℝ) - j)) =
      (-1 : ℝ) ^ n * oddDoubleFactorial n / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      norm_num [oddDoubleFactorial]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, pow_succ, pow_succ]
      simp only [oddDoubleFactorial, Finset.prod_range_succ]
      push_cast
      field_simp
      ring

private theorem choose_neg_half (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n =
      (-1 : ℝ) ^ n * oddDoubleFactorial n /
        ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) := by
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  have hsmeval :
      (descPochhammer ℤ n).smeval (-1 / 2 : ℝ) =
        ∏ j ∈ Finset.range n, ((-1 / 2 : ℝ) - j) := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [descPochhammer_succ_right, Polynomial.smeval_mul,
          Polynomial.smeval_sub, Polynomial.smeval_X,
          Polynomial.smeval_natCast, ih, Finset.prod_range_succ]
        simp
  rw [hsmeval, descProd_neg_half]
  field_simp

private theorem binomialCoefficient_hasSum
    (z : ℝ) (hz : |z| < 1) :
    HasSum
      (fun n : ℕ => binomialCoefficient n * z ^ n)
      (1 / Real.sqrt (1 - z)) := by
  have hseries :=
    Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := (-1 / 2 : ℝ))
  have hzmem : -z ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one]
    simpa [Real.norm_eq_abs, abs_neg] using hz
  have hs := hseries.hasSum hzmem
  have hterm : ∀ n : ℕ,
      (binomialSeries ℝ (-1 / 2 : ℝ) n) (fun _ => -z) =
        binomialCoefficient n * z ^ n := by
    intro n
    rw [binomialSeries_apply, choose_neg_half]
    simp only [List.ofFn_const, List.prod_replicate, smul_eq_mul]
    unfold binomialCoefficient
    rw [evenDoubleFactorial_eq,
      show -z = (-1 : ℝ) * z by ring, mul_pow]
    field_simp
    have hsign :
        (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    rw [pow_two, hsign]
    ring
  have hbase : 0 < 1 - z := by
    have hz' : z < 1 := le_abs_self z |>.trans_lt hz
    linarith
  have hvalue :
      (1 + -z) ^ (-1 / 2 : ℝ) =
        1 / Real.sqrt (1 - z) := by
    rw [show 1 + -z = 1 - z by ring, Real.sqrt_eq_rpow]
    rw [one_div, ← Real.rpow_neg hbase.le]
    congr 1
    ring
  have hs' :
      HasSum
        (fun n => (binomialSeries ℝ (-1 / 2 : ℝ) n) (fun _ => -z))
        ((1 + -z) ^ (-1 / 2 : ℝ)) := by
    simpa only [zero_add] using hs
  rw [hvalue] at hs'
  exact hs'.congr_fun (fun n => (hterm n).symm)

private theorem integrand_series_eq (t : ℝ) (ht : |t| < 1) :
    1 / Real.sqrt (1 - t ^ 4) =
      1 + ∑' k, integrandSeriesTerm t k := by
  have hz : |t ^ 4| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg t) ht (by norm_num)
  have hs := binomialCoefficient_hasSum (t ^ 4) hz
  calc
    1 / Real.sqrt (1 - t ^ 4) =
        ∑' n : ℕ, binomialCoefficient n * (t ^ 4) ^ n :=
      hs.tsum_eq.symm
    _ = binomialCoefficient 0 * (t ^ 4) ^ 0 +
        ∑' k : ℕ, binomialCoefficient (k + 1) * (t ^ 4) ^ (k + 1) :=
      hs.summable.tsum_eq_zero_add
    _ = 1 + ∑' k, integrandSeriesTerm t k := by
      congr 1
      · norm_num [binomialCoefficient, oddDoubleFactorial,
          evenDoubleFactorial]
      · apply tsum_congr
        intro k
        simp only [integrandSeriesTerm]
        rw [pow_mul]

private def fullTerm (t : ℝ) (n : ℕ) : ℝ :=
  binomialCoefficient n * t ^ (4 * n)

private theorem binomialCoefficient_nonneg (n : ℕ) :
    0 ≤ binomialCoefficient n := by
  unfold binomialCoefficient oddDoubleFactorial evenDoubleFactorial
  positivity

private theorem abs_le_endpoint {x t : ℝ} (ht : t ∈ Set.uIcc 0 x) :
    |t| ≤ |x| := by
  rcases Set.mem_uIcc.mp ht with hpos | hneg
  · rw [abs_of_nonneg hpos.1,
      abs_of_nonneg (hpos.1.trans hpos.2)]
    exact hpos.2
  · rw [abs_of_nonpos hneg.2,
      abs_of_nonpos (hneg.1.trans hneg.2)]
    linarith

private theorem fullTerm_integral_hasSum
    (x : ℝ) (hx : |x| < 1) :
    HasSum
      (fun n : ℕ => ∫ t in (0 : ℝ)..x, fullTerm t n)
      (∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 - t ^ 4)) := by
  let bound : ℕ → ℝ → ℝ :=
    fun n _ => binomialCoefficient n * |x| ^ (4 * n)
  have hbound_sum :
      Summable
        (fun n : ℕ => binomialCoefficient n * |x| ^ (4 * n)) := by
    have hz : |(|x| ^ 4)| < 1 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ |x| ^ 4)]
      exact pow_lt_one₀ (abs_nonneg x) hx (by norm_num)
    have hs := (binomialCoefficient_hasSum (|x| ^ 4) hz).summable
    simpa only [pow_mul] using hs
  apply intervalIntegral.hasSum_integral_of_dominated_convergence bound
  · intro n
    have hc : Continuous (fun t : ℝ => fullTerm t n) := by
      unfold fullTerm
      fun_prop
    exact hc.aestronglyMeasurable
  · intro n
    filter_upwards with t ht
    have htx : |t| ≤ |x| :=
      abs_le_endpoint (Set.uIoc_subset_uIcc ht)
    calc
      ‖fullTerm t n‖ =
          binomialCoefficient n * |t| ^ (4 * n) := by
        rw [fullTerm, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (binomialCoefficient_nonneg n), abs_pow]
      _ ≤ binomialCoefficient n * |x| ^ (4 * n) := by
        exact
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg t) htx _)
            (binomialCoefficient_nonneg n)
      _ = bound n t := by rfl
  · filter_upwards with t ht
    simpa only [bound] using hbound_sum
  · change
      IntervalIntegrable
        (fun _ : ℝ =>
          ∑' n : ℕ, binomialCoefficient n * |x| ^ (4 * n))
        MeasureTheory.volume 0 x
    exact intervalIntegrable_const
  · filter_upwards with t ht
    have htx : |t| < 1 :=
      (abs_le_endpoint (Set.uIoc_subset_uIcc ht)).trans_lt hx
    have hz : |t ^ 4| < 1 := by
      rw [abs_pow]
      exact pow_lt_one₀ (abs_nonneg t) htx (by norm_num)
    simpa only [fullTerm, pow_mul] using
      binomialCoefficient_hasSum (t ^ 4) hz

private theorem integral_fullTerm (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, fullTerm t n) =
      binomialCoefficient n * x ^ (4 * n + 1) /
        (4 * n + 1 : ℝ) := by
  unfold fullTerm
  rw [intervalIntegral.integral_const_mul,
    integral_pow]
  norm_num
  ring

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 - t ^ 4)) =
        ∫ t in (0 : ℝ)..x, 1 + ∑' k, integrandSeriesTerm t k := by
  intro x hx
  apply intervalIntegral.integral_congr
  intro t ht
  apply integrand_series_eq
  have htx : |t| ≤ |x| := by
    rcases Set.mem_uIcc.mp ht with hpos | hneg
    · rw [abs_of_nonneg hpos.1,
        abs_of_nonneg (hpos.1.trans hpos.2)]
      exact hpos.2
    · rw [abs_of_nonpos hneg.2,
        abs_of_nonpos (hneg.1.trans hneg.2)]
      linarith
  exact htx.trans_lt hx

theorem gap2 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 - t ^ 4)) =
        x + ∑' k, integratedSeriesTerm x k := by
  intro x hx
  have hs := fullTerm_integral_hasSum x hx
  calc
    (∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 - t ^ 4)) =
        ∑' n : ℕ, ∫ t in (0 : ℝ)..x, fullTerm t n :=
      hs.tsum_eq.symm
    _ = (∫ t in (0 : ℝ)..x, fullTerm t 0) +
        ∑' k : ℕ, ∫ t in (0 : ℝ)..x, fullTerm t (k + 1) :=
      hs.summable.tsum_eq_zero_add
    _ = x + ∑' k, integratedSeriesTerm x k := by
      congr 1
      · simpa [binomialCoefficient, oddDoubleFactorial,
          evenDoubleFactorial] using integral_fullTerm x 0
      · apply tsum_congr
        intro k
        simpa only [integratedSeriesTerm] using
          integral_fullTerm x (k + 1)

end

end ProofGap.Exercise2902
