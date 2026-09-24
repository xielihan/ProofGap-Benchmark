import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace ProofGap.Exercise2933

noncomputable section

open scoped BigOperators Interval

def y (x : ℝ) : ℝ :=
  Real.sin x

def arcLength : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi,
    Real.sqrt (1 + deriv y x ^ 2)

def halfArcIntegrand (x : ℝ) : ℝ :=
  Real.sqrt (1 + Real.cos x ^ 2)

def binomialCoefficient (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, ((1 / 2 : ℝ) - (k : ℝ))) /
    (Nat.factorial n : ℝ)

def binomialTerm (n : ℕ) (x : ℝ) : ℝ :=
  binomialCoefficient n * Real.cos x ^ (2 * n)

def cosinePowerIntegral (n : ℕ) : ℝ :=
  Real.pi * (Nat.factorial (2 * n) : ℝ) /
    ((2 : ℝ) ^ (2 * n + 1) *
      (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))

def arcContribution (n : ℕ) : ℝ :=
  2 * binomialCoefficient n * cosinePowerIntegral n

def normalizedTerm (n : ℕ) : ℝ :=
  binomialCoefficient n *
    (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n

def partialArcLength : ℝ :=
  Real.pi * ∑ n ∈ Finset.range 4, normalizedTerm n

def remainder : ℝ :=
  |arcLength - partialArcLength|

def firstOmittedBound : ℝ :=
  (3 * 5 * 2 * Real.pi) /
      ((Nat.factorial 4 : ℝ) * 2 ^ 4) *
    (Nat.factorial 8 : ℝ) /
      (2 ^ 9 * (Nat.factorial 4 : ℝ) * (Nat.factorial 4 : ℝ))

def roughValue : ℝ :=
  (314 / 100 : ℝ) *
    (1 + (25 / 100 : ℝ) - (5 / 100 : ℝ) + (2 / 100 : ℝ))

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem halfArcIntegrand_continuous : Continuous halfArcIntegrand := by
  unfold halfArcIntegrand
  fun_prop

private theorem cosinePowerIntegral_eq_integral (n : ℕ) :
    (∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos x ^ (2 * n)) =
      cosinePowerIntegral n := by
  induction n with
  | zero =>
      simp [cosinePowerIntegral]
  | succ n ih =>
      have hrec := integral_cos_pow
        (a := (0 : ℝ)) (b := Real.pi / 2) (n := 2 * n)
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, hrec]
      simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_pow,
        Nat.succ_ne_zero, Real.cos_zero, Real.sin_zero, one_pow, mul_one,
        mul_zero, sub_zero, zero_div, zero_add, ih]
      unfold cosinePowerIntegral
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]
      simp only [Nat.factorial_succ]
      push_cast
      norm_num [pow_add]
      field_simp [show (Nat.factorial n : ℝ) ≠ 0 by positivity,
        show (n : ℝ) + 1 ≠ 0 by positivity]
      ring

private theorem binomialCoefficient_eq_choose (n : ℕ) :
    binomialCoefficient n = Ring.choose (1 / 2 : ℝ) n := by
  have hprod :
      (descPochhammer ℤ n).smeval (1 / 2 : ℝ) =
        ∏ k ∈ Finset.range n, ((1 / 2 : ℝ) - (k : ℝ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [descPochhammer_succ_right, Polynomial.smeval_mul,
          Finset.prod_range_succ, ih]
        simp only [Polynomial.smeval_sub, Polynomial.smeval_X,
          Polynomial.smeval_natCast, pow_zero, nsmul_eq_mul, mul_one]
        push_cast
        ring
  have h := Ring.descPochhammer_eq_factorial_smul_choose (1 / 2 : ℝ) n
  rw [nsmul_eq_mul] at h
  rw [hprod] at h
  unfold binomialCoefficient
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  rw [h]
  field_simp [hfac]

private theorem halfArcIntegrand_hasSum (x : ℝ)
    (hx : |Real.cos x| < 1) :
    HasSum (fun n : ℕ => binomialTerm n x) (halfArcIntegrand x) := by
  have hz : Real.cos x ^ 2 ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one]
    rw [Real.norm_eq_abs, abs_sq]
    rw [← sq_abs]
    nlinarith [abs_nonneg (Real.cos x)]
  have hs :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := (1 / 2 : ℝ))).hasSum_sub hz
  convert hs using 1
  · funext n
    rw [binomialTerm, binomialCoefficient_eq_choose]
    rw [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [sub_zero, smul_eq_mul]
    rw [pow_mul]
  · unfold halfArcIntegrand
    simpa only [one_div] using Real.sqrt_eq_rpow (1 + Real.cos x ^ 2)

private theorem cos_abs_lt_one_of_mem_halfOpen
    {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    |Real.cos x| < 1 := by
  have hcos_nonneg : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
  rw [abs_of_nonneg hcos_nonneg]
  simpa using Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    (x := (0 : ℝ)) (y := x) (by norm_num) hx.2 hx.1

private theorem arcLength_eq_halfIntegral :
    arcLength =
      2 * ∫ x in (0 : ℝ)..(Real.pi / 2), halfArcIntegrand x := by
  have hderiv (x : ℝ) : deriv y x = Real.cos x := by
    exact (Real.hasDerivAt_sin x).deriv
  have hleft : IntervalIntegrable halfArcIntegrand MeasureTheory.volume
      (0 : ℝ) (Real.pi / 2) := halfArcIntegrand_continuous.intervalIntegrable _ _
  have hright : IntervalIntegrable halfArcIntegrand MeasureTheory.volume
      (Real.pi / 2) Real.pi := halfArcIntegrand_continuous.intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ x in Real.pi / 2..Real.pi, halfArcIntegrand x) =
        ∫ x in (0 : ℝ)..Real.pi / 2, halfArcIntegrand x := by
    calc
      (∫ x in Real.pi / 2..Real.pi, halfArcIntegrand x) =
          ∫ x in (0 : ℝ)..Real.pi / 2,
            halfArcIntegrand (Real.pi - x) := by
        symm
        have h := intervalIntegral.integral_comp_sub_left
          (f := halfArcIntegrand) (a := (0 : ℝ))
            (b := Real.pi / 2) Real.pi
        have heq : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
        rw [heq, sub_zero] at h
        exact h
      _ = ∫ x in (0 : ℝ)..Real.pi / 2, halfArcIntegrand x := by
        apply intervalIntegral.integral_congr
        intro x hx
        unfold halfArcIntegrand
        change Real.sqrt (1 + Real.cos (Real.pi - x) ^ 2) = _
        rw [Real.cos_pi_sub]
        congr 1
        ring
  unfold arcLength
  calc
    (∫ x in (0 : ℝ)..Real.pi,
        Real.sqrt (1 + deriv y x ^ 2)) =
        ∫ x in (0 : ℝ)..Real.pi, halfArcIntegrand x := by
      apply intervalIntegral.integral_congr
      intro x hx
      change Real.sqrt (1 + deriv y x ^ 2) = halfArcIntegrand x
      rw [hderiv]
      rfl
    _ = 2 * ∫ x in (0 : ℝ)..Real.pi / 2, halfArcIntegrand x := by
      rw [← hsplit, hreflect]
      ring

private theorem arcLength_eq_integral_tsum :
    arcLength =
      2 * ∫ x in (0 : ℝ)..(Real.pi / 2),
        ∑' n : ℕ, binomialTerm n x := by
  rw [arcLength_eq_halfIntegral]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hx
  exact (halfArcIntegrand_hasSum x
    (cos_abs_lt_one_of_mem_halfOpen hx)).tsum_eq.symm

private theorem binomialCoefficient_succ (n : ℕ) :
    binomialCoefficient (n + 1) =
      binomialCoefficient n * ((1 / 2 : ℝ) - n) / (n + 1 : ℕ) := by
  unfold binomialCoefficient
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hn]

private theorem cosinePowerIntegral_pos (n : ℕ) :
    0 < cosinePowerIntegral n := by
  unfold cosinePowerIntegral
  positivity

private theorem cosinePowerIntegral_succ (n : ℕ) :
    cosinePowerIntegral (n + 1) =
      cosinePowerIntegral n * ((2 * n + 1 : ℕ) : ℝ) /
        ((2 * n + 2 : ℕ) : ℝ) := by
  unfold cosinePowerIntegral
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  norm_num [pow_add]
  field_simp [show (Nat.factorial n : ℝ) ≠ 0 by positivity,
    show (n : ℝ) + 1 ≠ 0 by positivity]
  ring

private def arcRatio (m : ℕ) : ℝ :=
  (((2 * m - 1 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ)) /
    (4 * ((m + 1 : ℕ) : ℝ) ^ 2)

private theorem arcRatio_pos {m : ℕ} (hm : 1 ≤ m) : 0 < arcRatio m := by
  unfold arcRatio
  have hsub : 0 < 2 * m - 1 := by omega
  positivity

private theorem arcRatio_lt_one {m : ℕ} (hm : 1 ≤ m) : arcRatio m < 1 := by
  unfold arcRatio
  have hsub : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  push_cast
  rw [hsub]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : (0 : ℝ) < 4 * ((m : ℝ) + 1) ^ 2 := by positivity
  rw [div_lt_one hden]
  nlinarith

private theorem arcRatio_le_square {m : ℕ} (hm : 1 ≤ m) :
    arcRatio m ≤ ((m : ℝ) / (m + 1)) ^ 2 := by
  unfold arcRatio
  have hsub : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  push_cast
  rw [hsub]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm1]
  nlinarith

private theorem arcContribution_succ {m : ℕ} (hm : 1 ≤ m) :
    arcContribution (m + 1) = -arcContribution m * arcRatio m := by
  rw [arcContribution, binomialCoefficient_succ, cosinePowerIntegral_succ]
  unfold arcContribution arcRatio
  have hsub : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  push_cast
  rw [hsub]
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm1]
  ring

private def arcMagnitude (k : ℕ) : ℝ :=
  |arcContribution (k + 1)|

private theorem arcContribution_one :
    arcContribution 1 = Real.pi / 4 := by
  norm_num [arcContribution, binomialCoefficient, cosinePowerIntegral,
    Finset.prod_range_succ, Nat.factorial]
  ring

private theorem arcMagnitude_zero : arcMagnitude 0 = Real.pi / 4 := by
  rw [arcMagnitude, arcContribution_one, abs_of_pos (by positivity)]

private theorem arcMagnitude_succ (k : ℕ) :
    arcMagnitude (k + 1) = arcMagnitude k * arcRatio (k + 1) := by
  unfold arcMagnitude
  rw [arcContribution_succ (m := k + 1) (by omega), abs_mul, abs_neg,
    abs_of_pos (arcRatio_pos (m := k + 1) (by omega))]

private theorem arcMagnitude_pos (k : ℕ) : 0 < arcMagnitude k := by
  induction k with
  | zero => rw [arcMagnitude_zero]; positivity
  | succ k ih =>
      rw [arcMagnitude_succ]
      exact mul_pos ih (arcRatio_pos (m := k + 1) (by omega))

private theorem arcMagnitude_strictAnti : StrictAnti arcMagnitude := by
  apply strictAnti_nat_of_succ_lt
  intro k
  rw [arcMagnitude_succ]
  have hm := arcMagnitude_pos k
  have hr := arcRatio_lt_one (m := k + 1) (by omega)
  have hr0 := arcRatio_pos (m := k + 1) (by omega)
  nlinarith [mul_pos hm (sub_pos.mpr hr)]

private theorem arcMagnitude_le_majorant (k : ℕ) :
    arcMagnitude k ≤ Real.pi / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  induction k with
  | zero =>
      rw [arcMagnitude_zero]
      norm_num
      nlinarith [Real.pi_pos]
  | succ k ih =>
      rw [arcMagnitude_succ]
      have hr := arcRatio_le_square (m := k + 1) (by omega)
      have hr' : arcRatio (k + 1) ≤
          (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ^ 2 := by
        convert hr using 1 <;> push_cast <;> ring
      have hm : (0 : ℝ) ≤ arcMagnitude k := (arcMagnitude_pos k).le
      have hq : (0 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ^ 2 :=
        sq_nonneg _
      calc
        arcMagnitude k * arcRatio (k + 1) ≤
            (Real.pi / (((k + 1 : ℕ) : ℝ) ^ 2)) *
              ((((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ^ 2) := by
          exact mul_le_mul ih hr' (arcRatio_pos (m := k + 1) (by omega)).le
            (by positivity)
        _ = Real.pi / (((k + 1 + 1 : ℕ) : ℝ) ^ 2) := by
          have hk1 : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
          have hk2 : (((k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
          field_simp [hk1, hk2]

private theorem summable_arcMagnitude : Summable arcMagnitude := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ =>
      (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hbase
  have hmajorant : Summable (fun k : ℕ =>
      Real.pi / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [div_eq_mul_inv, one_mul] using hshift.mul_left Real.pi
  exact Summable.of_nonneg_of_le (fun k => (arcMagnitude_pos k).le)
    arcMagnitude_le_majorant hmajorant

private theorem summable_abs_arcContribution :
    Summable (fun n : ℕ => |arcContribution n|) := by
  apply (summable_nat_add_iff 1).1
  simpa only [arcMagnitude] using summable_arcMagnitude

private theorem summable_arcContribution : Summable arcContribution := by
  rw [← summable_norm_iff]
  simpa only [Real.norm_eq_abs] using summable_abs_arcContribution

private theorem integral_binomialTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi / 2, binomialTerm n x) =
      binomialCoefficient n * cosinePowerIntegral n := by
  unfold binomialTerm
  rw [intervalIntegral.integral_const_mul, cosinePowerIntegral_eq_integral]

private theorem integral_norm_binomialTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi / 2, ‖binomialTerm n x‖) =
      |arcContribution n| / 2 := by
  have heq : (fun x : ℝ => ‖binomialTerm n x‖) =
      fun x : ℝ => |binomialCoefficient n| * Real.cos x ^ (2 * n) := by
    funext x
    have hp : 0 ≤ Real.cos x ^ (2 * n) := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
      positivity
    rw [Real.norm_eq_abs, binomialTerm, abs_mul,
      abs_of_nonneg hp]
  rw [heq, intervalIntegral.integral_const_mul,
    cosinePowerIntegral_eq_integral]
  unfold arcContribution
  rw [abs_mul, abs_mul, abs_of_pos (cosinePowerIntegral_pos n)]
  norm_num
  ring

private theorem summable_integral_norm_binomialTerm :
    Summable (fun n : ℕ =>
      ∫ x in (0 : ℝ)..Real.pi / 2, ‖binomialTerm n x‖) := by
  apply (summable_abs_arcContribution.mul_right (1 / 2 : ℝ)).congr
  intro n
  rw [integral_norm_binomialTerm]
  ring

private theorem intervalIntegral_tsum_binomialTerm :
    (∫ x in (0 : ℝ)..Real.pi / 2, ∑' n : ℕ, binomialTerm n x) =
      ∑' n : ℕ, ∫ x in (0 : ℝ)..Real.pi / 2, binomialTerm n x := by
  have hint (n : ℕ) :
      MeasureTheory.IntegrableOn (binomialTerm n) (Set.Ioc (0 : ℝ) (Real.pi / 2)) := by
    have hc : Continuous (binomialTerm n) := by
      unfold binomialTerm
      fun_prop
    exact (hc.intervalIntegrable (0 : ℝ) (Real.pi / 2)).1
  have hnorm : Summable (fun n : ℕ =>
      ∫ x in Set.Ioc (0 : ℝ) (Real.pi / 2), ‖binomialTerm n x‖) := by
    simpa only [intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using
        summable_integral_norm_binomialTerm
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hint hnorm]
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le
    (μ := MeasureTheory.volume) (f := binomialTerm n)
    (by positivity : (0 : ℝ) ≤ Real.pi / 2)).symm

private theorem arcLength_eq_tsum_arcContribution :
    arcLength = ∑' n : ℕ, arcContribution n := by
  rw [arcLength_eq_integral_tsum, intervalIntegral_tsum_binomialTerm,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [integral_binomialTerm]
  unfold arcContribution
  ring

private theorem arcContribution_hasSum :
    HasSum arcContribution arcLength := by
  rw [arcLength_eq_tsum_arcContribution]
  exact summable_arcContribution.hasSum

private theorem cosinePowerIntegral_eq_choose (n : ℕ) :
    cosinePowerIntegral n =
      Real.pi / 2 * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n := by
  have hnat := Nat.choose_mul_factorial_mul_factorial
    (show n ≤ 2 * n by omega)
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hnat
  have hcast :
      (Nat.choose (2 * n) n : ℝ) * (Nat.factorial n : ℝ) *
          (Nat.factorial n : ℝ) = (Nat.factorial (2 * n) : ℝ) := by
    exact_mod_cast hnat
  have hfour : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, pow_mul]
  unfold cosinePowerIntegral
  rw [hfour, show 2 * n + 1 = 2 * n + 1 by rfl, pow_succ]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hp : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
  field_simp [hf, hp]
  nlinarith

private theorem arcContribution_eq_normalized (n : ℕ) :
    arcContribution n = Real.pi * normalizedTerm n := by
  rw [arcContribution, cosinePowerIntegral_eq_choose]
  unfold normalizedTerm
  ring

private theorem arcContribution_zero : arcContribution 0 = Real.pi := by
  norm_num [arcContribution, binomialCoefficient, cosinePowerIntegral,
    Finset.prod_range_succ, Nat.factorial]
  ring

private theorem arcContribution_shifted_sign (k : ℕ) :
    arcContribution (k + 1) = (-1 : ℝ) ^ k * arcMagnitude k := by
  induction k with
  | zero =>
      rw [arcContribution_one, arcMagnitude_zero]
      norm_num
  | succ k ih =>
      rw [arcContribution_succ (m := k + 1) (by omega), ih,
        arcMagnitude_succ, pow_succ]
      ring

private theorem alternatingTail_tendsto :
    Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * arcMagnitude i)
      Filter.atTop (nhds (arcLength - arcContribution 0)) := by
  have ht := (hasSum_nat_add_iff' 1).2 arcContribution_hasSum
  convert ht.tendsto_sum_nat using 1
  · funext n
    apply Finset.sum_congr rfl
    intro i hi
    exact (arcContribution_shifted_sign i).symm
  · simp

private theorem partialArcLength_eq_sum :
    partialArcLength = ∑ n ∈ Finset.range 4, arcContribution n := by
  unfold partialArcLength
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact (arcContribution_eq_normalized n).symm

private theorem firstOmittedBound_eq_arcMagnitude :
    firstOmittedBound = arcMagnitude 3 := by
  rw [arcMagnitude]
  norm_num [arcContribution, binomialCoefficient, cosinePowerIntegral,
    firstOmittedBound, Finset.prod_range_succ, Nat.factorial,
    abs_of_neg (neg_lt_zero.mpr Real.pi_pos)]
  rw [abs_of_pos (by positivity :
    (0 : ℝ) < Real.pi * 40320 / 294912)]
  ring

private theorem arcLength_lt_partialArcLength :
    arcLength < partialArcLength := by
  have hu := arcMagnitude_strictAnti.antitone.tendsto_le_alternating_series
    alternatingTail_tendsto 2
  simp_rw [← arcContribution_shifted_sign] at hu
  rw [partialArcLength_eq_sum]
  norm_num [arcContribution_zero, arcContribution, binomialCoefficient,
    cosinePowerIntegral, Finset.sum_range_succ, Finset.prod_range_succ,
    Nat.factorial] at hu ⊢
  nlinarith [Real.pi_pos]

private def rationalMagnitude : ℕ → ℝ
  | 0 => 1 / 4
  | k + 1 => rationalMagnitude k * arcRatio (k + 1)

private theorem arcMagnitude_eq_rationalMagnitude (k : ℕ) :
    arcMagnitude k = Real.pi * rationalMagnitude k := by
  induction k with
  | zero =>
      rw [arcMagnitude_zero]
      norm_num [rationalMagnitude]
      ring
  | succ k ih =>
      rw [arcMagnitude_succ, ih]
      simp only [rationalMagnitude]
      ring

set_option maxRecDepth 100000 in
private theorem arcLength_numeric_bounds :
    (382 / 100 : ℝ) < arcLength ∧ arcLength < (384 / 100 : ℝ) := by
  have hl := arcMagnitude_strictAnti.antitone.alternating_series_le_tendsto
    alternatingTail_tendsto 19
  have hu := arcMagnitude_strictAnti.antitone.tendsto_le_alternating_series
    alternatingTail_tendsto 2
  simp_rw [arcMagnitude_eq_rationalMagnitude] at hl hu
  rw [arcContribution_zero] at hl hu
  norm_num [rationalMagnitude, arcRatio, Finset.sum_range_succ] at hl hu
  constructor
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]

theorem gap1 :
    arcLength =
      ∫ x in (0 : ℝ)..Real.pi,
        Real.sqrt (1 + deriv y x ^ 2) := by
  rfl

theorem gap2 :
    (∫ x in (0 : ℝ)..Real.pi,
        Real.sqrt (1 + deriv y x ^ 2)) =
      2 * ∫ x in (0 : ℝ)..(Real.pi / 2), halfArcIntegrand x := by
  rw [← gap1]
  exact arcLength_eq_halfIntegral

theorem gap3 :
    arcLength =
      2 * ∫ x in (0 : ℝ)..(Real.pi / 2), halfArcIntegrand x := by
  exact arcLength_eq_halfIntegral

theorem gap4 :
    arcLength =
      2 * ∫ x in (0 : ℝ)..(Real.pi / 2),
        ∑' n : ℕ, binomialTerm n x := by
  exact arcLength_eq_integral_tsum

theorem gap5 :
    ∀ n : ℕ,
      (∫ x in (0 : ℝ)..(Real.pi / 2),
          Real.cos x ^ (2 * n)) =
        cosinePowerIntegral n := by
  exact cosinePowerIntegral_eq_integral

theorem gap6 :
    arcLength = ∑' n : ℕ, arcContribution n := by
  exact arcLength_eq_tsum_arcContribution

theorem gap7 :
    arcLength = Real.pi * ∑' n : ℕ, normalizedTerm n := by
  rw [arcLength_eq_tsum_arcContribution, ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact arcContribution_eq_normalized n

theorem gap8 :
    0 < remainder := by
  unfold remainder
  exact abs_pos.mpr (sub_ne_zero.mpr
    (ne_of_lt arcLength_lt_partialArcLength))

theorem gap9 :
    remainder < firstOmittedBound := by
  have hl := arcMagnitude_strictAnti.antitone.alternating_series_le_tendsto
    alternatingTail_tendsto 3
  simp_rw [← arcContribution_shifted_sign] at hl
  norm_num [Finset.sum_range_succ] at hl
  rw [arcContribution_shifted_sign 3, arcContribution_shifted_sign 4,
    arcContribution_shifted_sign 5] at hl
  norm_num at hl
  have hpair : arcMagnitude 5 < arcMagnitude 4 :=
    arcMagnitude_strictAnti (by omega)
  rw [remainder, abs_of_neg (sub_neg.mpr arcLength_lt_partialArcLength),
    firstOmittedBound_eq_arcMagnitude]
  rw [partialArcLength_eq_sum]
  norm_num [Finset.sum_range_succ] at hl ⊢
  nlinarith

theorem gap10 :
    firstOmittedBound < (4 / 100 : ℝ) := by
  norm_num [firstOmittedBound, Nat.factorial]
  nlinarith [Real.pi_lt_d2]

theorem gap11 :
    (0 : ℝ) < 4 / 100 := by
  norm_num

theorem gap12 :
    Approx arcLength roughValue (4 / 100 : ℝ) := by
  rcases arcLength_numeric_bounds with ⟨hl, hu⟩
  rw [Approx, abs_lt]
  norm_num [roughValue] at hl hu ⊢
  constructor <;> linarith

theorem gap13 :
    Approx roughValue (383 / 100 : ℝ)
      (1 / 100 : ℝ) := by
  norm_num [Approx, roughValue, abs_lt]

theorem gap14 :
    Approx arcLength (383 / 100 : ℝ)
      (1 / 100 : ℝ) := by
  rcases arcLength_numeric_bounds with ⟨hl, hu⟩
  rw [Approx, abs_lt]
  norm_num at hl hu ⊢
  constructor <;> linarith

end

end ProofGap.Exercise2933
