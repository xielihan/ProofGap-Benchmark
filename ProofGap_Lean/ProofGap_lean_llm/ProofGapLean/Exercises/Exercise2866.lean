import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2866

noncomputable section

def negativeThreeHalvesFalling (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (-(3 / 2 : ℝ) - k)

def generalizedTerm (x : ℝ) (n : ℕ) : ℝ :=
  negativeThreeHalvesFalling n / (Nat.factorial n : ℝ) * (-x ^ 2) ^ n

def oddProductThrough (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), (2 * k + 1 : ℕ)

def evenProductThrough (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * (k + 1) : ℕ)

def doubleFactorialTerm (x : ℝ) (n : ℕ) : ℝ :=
  oddProductThrough n / evenProductThrough n * x ^ (2 * n)

private theorem negativeThreeHalvesFalling_eq_smeval (n : ℕ) :
    negativeThreeHalvesFalling n =
      (descPochhammer ℤ n).smeval (-(3 / 2 : ℝ)) := by
  induction n with
  | zero =>
      simp [negativeThreeHalvesFalling, descPochhammer_zero]
  | succ n ih =>
      have hfall :
          negativeThreeHalvesFalling (n + 1) =
            negativeThreeHalvesFalling n * (-(3 / 2 : ℝ) - n) := by
        simp [negativeThreeHalvesFalling, Finset.prod_range_succ]
      rw [hfall, ih, descPochhammer_succ_right,
        Polynomial.smeval_mul]
      simp [Polynomial.smeval_natCast]

private theorem negativeThreeHalvesFalling_div_factorial (n : ℕ) :
    negativeThreeHalvesFalling n / (Nat.factorial n : ℝ) =
      Ring.choose (-(3 / 2 : ℝ)) n := by
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  rw [← negativeThreeHalvesFalling_eq_smeval]
  ring

private theorem negativeThreeHalvesFalling_formula (n : ℕ) :
    negativeThreeHalvesFalling n =
      oddProductThrough n / (-2 : ℝ) ^ n := by
  induction n with
  | zero =>
      norm_num [negativeThreeHalvesFalling, oddProductThrough]
  | succ n ih =>
      have hfall :
          negativeThreeHalvesFalling (n + 1) =
            negativeThreeHalvesFalling n * (-(3 / 2 : ℝ) - n) := by
        simp [negativeThreeHalvesFalling, Finset.prod_range_succ]
      have hodd :
          oddProductThrough (n + 1) =
            oddProductThrough n * (2 * (n + 1) + 1 : ℕ) := by
        simp [oddProductThrough, Finset.prod_range_succ]
      rw [hfall, hodd, ih, pow_succ]
      push_cast
      ring

private theorem evenProductThrough_formula (n : ℕ) :
    evenProductThrough n = (2 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
  induction n with
  | zero =>
      norm_num [evenProductThrough]
  | succ n ih =>
      have heven :
          evenProductThrough (n + 1) =
            evenProductThrough n * (2 * (n + 1) : ℕ) := by
        simp [evenProductThrough, Finset.prod_range_succ]
      rw [heven, ih, pow_succ, Nat.factorial_succ]
      push_cast
      ring

private theorem generalizedTerm_eq_doubleFactorialTerm (x : ℝ) (n : ℕ) :
    generalizedTerm x n = doubleFactorialTerm x n := by
  have hxpow :
      (-x ^ 2) ^ n = (-1 : ℝ) ^ n * x ^ (2 * n) := by
    calc
      (-x ^ 2) ^ n = ((-1 : ℝ) * x ^ 2) ^ n := by
        congr 1
        ring
      _ = (-1 : ℝ) ^ n * (x ^ 2) ^ n := mul_pow _ _ _
      _ = (-1 : ℝ) ^ n * x ^ (2 * n) := by rw [← pow_mul]
  have htwo :
      (-2 : ℝ) ^ n = (-1 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (-2 : ℝ) = (-1 : ℝ) * 2 by ring, mul_pow]
  rw [generalizedTerm, doubleFactorialTerm,
    negativeThreeHalvesFalling_formula, evenProductThrough_formula,
    hxpow, htwo]
  have hm : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hm, h2, hf]

private theorem generalizedTerm_hasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (generalizedTerm x)
      (Real.rpow (1 - x ^ 2) (-(3 / 2 : ℝ))) := by
  have hzabs : |-x ^ 2| < 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg x)]
    nlinarith [sq_abs x, abs_nonneg x]
  have hz : -x ^ 2 ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq]
    rw [ENNReal.ofReal_lt_one, sub_zero]
    exact hzabs
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := -(3 / 2 : ℝ))).hasSum hz
  simp only [Real.rpow_eq_pow]
  convert h using 1 with n
  · funext n
    unfold generalizedTerm
    rw [negativeThreeHalvesFalling_div_factorial]
    simp [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm]
  · norm_num
    ring_nf

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      1 / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)) =
        Real.rpow (1 - x ^ 2) (-(3 / 2 : ℝ)) := by
  intro x hx
  have hpos : 0 < 1 - x ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x]
  rw [one_div]
  simp only [Real.rpow_eq_pow]
  calc
    ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2))⁻¹ =
        (((1 - x ^ 2) ^ (1 : ℝ)) *
          ((1 - x ^ 2) ^ (1 / 2 : ℝ)))⁻¹ := by
            rw [Real.sqrt_eq_rpow, Real.rpow_one]
    _ = ((1 - x ^ 2) ^ (1 + 1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_add hpos]
    _ = (1 - x ^ 2) ^ (-(1 + 1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hpos.le]
    _ = (1 - x ^ 2) ^ (-(3 / 2 : ℝ)) := by norm_num

theorem gap2
    (hrpow :
      ∀ x : ℝ, |x| < 1 →
        1 / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)) =
          Real.rpow (1 - x ^ 2) (-(3 / 2 : ℝ))) :
    ∀ x : ℝ, |x| < 1 →
      1 / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)) =
        ∑' n, generalizedTerm x n := by
  intro x hx
  exact (hrpow x hx).trans (generalizedTerm_hasSum x hx).tsum_eq.symm

theorem gap3
    (hrpow :
      ∀ x : ℝ, |x| < 1 →
        1 / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)) =
          Real.rpow (1 - x ^ 2) (-(3 / 2 : ℝ)))
    (hgeneralized :
      ∀ x : ℝ, |x| < 1 →
        1 / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)) =
          ∑' n, generalizedTerm x n) :
    ∀ x : ℝ, |x| < 1 →
      1 / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)) =
        ∑' n, doubleFactorialTerm x n := by
  intro x hx
  exact (hgeneralized x hx).trans
    (tsum_congr (generalizedTerm_eq_doubleFactorialTerm x))

end

end ProofGap.Exercise2866
