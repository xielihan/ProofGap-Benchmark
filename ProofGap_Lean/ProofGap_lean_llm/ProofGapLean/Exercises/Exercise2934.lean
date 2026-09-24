import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace ProofGap.Exercise2934

noncomputable section

open scoped BigOperators Interval

def a : ℝ := 1

def b : ℝ := 1 / 2

def x (t : ℝ) : ℝ :=
  a * Real.sin t

def y (t : ℝ) : ℝ :=
  b * Real.cos t

def speed (t : ℝ) : ℝ :=
  Real.sqrt (deriv x t ^ 2 + deriv y t ^ 2)

def eccentricity : ℝ :=
  Real.sqrt (a ^ 2 - b ^ 2) / a

def perimeter : ℝ :=
  4 * a * ∫ t in (0 : ℝ)..(Real.pi / 2),
    Real.sqrt (1 - eccentricity ^ 2 * Real.sin t ^ 2)

def binomialCoefficient (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, ((1 / 2 : ℝ) - (k : ℝ))) /
    (Nat.factorial n : ℝ)

def integrandTerm (e : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  binomialCoefficient n * (-e ^ 2) ^ n * Real.sin t ^ (2 * n)

def sinePowerIntegral (n : ℕ) : ℝ :=
  Real.pi * (Nat.factorial (2 * n) : ℝ) /
    ((2 : ℝ) ^ (2 * n + 1) *
      (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))

def integratedTerm (e : ℝ) (n : ℕ) : ℝ :=
  4 * a * binomialCoefficient n * (-e ^ 2) ^ n *
    sinePowerIntegral n

def normalizedTerm (n : ℕ) : ℝ :=
  binomialCoefficient n * (-eccentricity ^ 2) ^ n *
    (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n

def approximationError : ℝ :=
  |perimeter - (484 / 100 : ℝ)|

def roughFourTerm : ℝ :=
  2 * Real.pi *
    (1 - (188 / 1000 : ℝ) - (26 / 1000 : ℝ) -
      (8 / 1000 : ℝ) - (3 / 1000 : ℝ))

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem deriv_x (t : ℝ) :
    deriv x t = a * Real.cos t := by
  unfold x
  exact (Real.hasDerivAt_sin t).const_mul a |>.deriv

private theorem deriv_y (t : ℝ) :
    deriv y t = -(b * Real.sin t) := by
  unfold y
  convert (Real.hasDerivAt_cos t).const_mul b |>.deriv using 1
  ring
private theorem eccentricity_sq :
    eccentricity ^ 2 = 3 / 4 := by
  unfold eccentricity a b
  convert Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 4) using 1 <;>
    norm_num

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

private theorem binomialCoefficient_succ (n : ℕ) :
    binomialCoefficient (n + 1) =
      binomialCoefficient n * ((1 / 2 : ℝ) - n) / (n + 1) := by
  unfold binomialCoefficient
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hn]

private theorem binomialCoefficient_eq_ringChoose (n : ℕ) :
    binomialCoefficient n = Ring.choose (1 / 2 : ℝ) n := by
  induction n with
  | zero =>
      norm_num [binomialCoefficient, Ring.choose_zero_right]
  | succ n ih =>
      rw [binomialCoefficient_succ, ringChoose_succ, ih]

private theorem binomialCoefficient_abs_succ_le (n : ℕ) :
    |binomialCoefficient (n + 1)| ≤ |binomialCoefficient n| := by
  rw [binomialCoefficient_succ, abs_div, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hratio :
      |(1 / 2 : ℝ) - n| ≤ (n : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  nlinarith [mul_le_mul_of_nonneg_left hratio
    (abs_nonneg (binomialCoefficient n))]

private theorem binomialCoefficient_abs_le_one (n : ℕ) :
    |binomialCoefficient n| ≤ 1 := by
  induction n with
  | zero =>
      norm_num [binomialCoefficient]
  | succ n ih =>
      exact (binomialCoefficient_abs_succ_le n).trans ih

private theorem integral_sin_even_eq_sinePowerIntegral (n : ℕ) :
    (∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin t ^ (2 * n)) =
      sinePowerIntegral n := by
  induction n with
  | zero =>
      norm_num [sinePowerIntegral]
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega,
        integral_sin_pow, Real.sin_zero, Real.cos_zero,
        Real.sin_pi_div_two, Real.cos_pi_div_two, ih]
      simp only [zero_pow, Nat.succ_ne_zero, zero_mul, one_pow,
        mul_zero, sub_zero, zero_div, zero_add]
      unfold sinePowerIntegral
      push_cast
      rw [Nat.factorial_succ, show 2 * (n + 1) =
        (2 * n + 1) + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2n : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hf, hn1, h2n]
      ring

private theorem eccentricity_nonneg :
    0 ≤ eccentricity := by
  unfold eccentricity a b
  positivity

private theorem eccentricity_abs_lt_one :
    |eccentricity| < 1 := by
  rw [abs_of_nonneg eccentricity_nonneg]
  nlinarith [eccentricity_sq, sq_nonneg eccentricity]

private theorem integrandTerm_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => integrandTerm eccentricity n t)
      (Real.sqrt
        (1 - eccentricity ^ 2 * Real.sin t ^ 2)) := by
  let z : ℝ := -(eccentricity ^ 2) * Real.sin t ^ 2
  have hsin : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  have hsinpow : |Real.sin t| ^ 2 ≤ 1 := by
    exact pow_le_one₀ (abs_nonneg (Real.sin t)) hsin
  have heabs : |eccentricity| ^ 2 = 3 / 4 := by
    rw [← abs_pow, eccentricity_sq,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  have hzabs : |z| < 1 := by
    dsimp [z]
    rw [abs_mul, abs_neg, abs_pow, abs_pow, heabs]
    nlinarith [sq_nonneg (abs (Real.sin t))]
  have hz : z ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one]
    simpa [Real.norm_eq_abs] using hzabs
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := (1 / 2 : ℝ))).hasSum hz
  have hfun :
      (fun n : ℕ =>
        (binomialSeries ℝ (1 / 2 : ℝ) n)
          (fun _ => z)) =
        fun n : ℕ => integrandTerm eccentricity n t := by
    funext n
    rw [binomialSeries_apply]
    simp only [smul_eq_mul]
    rw [show (List.ofFn (fun _ : Fin n => z)).prod = z ^ n by simp]
    unfold integrandTerm
    rw [binomialCoefficient_eq_ringChoose]
    dsimp [z]
    rw [mul_pow, pow_mul]
    ring
  rw [hfun] at h
  simpa [Real.sqrt_eq_rpow, sub_eq_add_neg, z] using h

private theorem integrandTerm_norm_le_geometric (t : ℝ) (n : ℕ) :
    ‖integrandTerm eccentricity n t‖ ≤ (3 / 4 : ℝ) ^ n := by
  have hbc := binomialCoefficient_abs_le_one n
  have hsin :
      |Real.sin t| ^ (2 * n) ≤ 1 := by
    exact pow_le_one₀ (abs_nonneg (Real.sin t))
      (Real.abs_sin_le_one t)
  have hprod :
      |binomialCoefficient n| * |Real.sin t| ^ (2 * n) ≤ 1 := by
    have h := mul_le_mul hbc hsin
      (by positivity : 0 ≤ |Real.sin t| ^ (2 * n))
      (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  rw [Real.norm_eq_abs]
  unfold integrandTerm
  rw [eccentricity_sq, abs_mul, abs_mul, abs_pow, abs_pow,
    abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  calc
    |binomialCoefficient n| * (3 / 4 : ℝ) ^ n *
        |Real.sin t| ^ (2 * n) =
        (3 / 4 : ℝ) ^ n *
          (|binomialCoefficient n| * |Real.sin t| ^ (2 * n)) := by
      ring
    _ ≤ (3 / 4 : ℝ) ^ n * 1 :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (3 / 4 : ℝ) ^ n := by ring

private theorem integrandIntegral_hasSum :
    HasSum
      (fun n : ℕ =>
        ∫ t in (0 : ℝ)..(Real.pi / 2),
          integrandTerm eccentricity n t)
      (∫ t in (0 : ℝ)..(Real.pi / 2),
        Real.sqrt
          (1 - eccentricity ^ 2 * Real.sin t ^ 2)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => (3 / 4 : ℝ) ^ n)
  · intro n
    apply Continuous.aestronglyMeasurable
    unfold integrandTerm
    fun_prop
  · intro n
    filter_upwards with t ht
    exact integrandTerm_norm_le_geometric t n
  · filter_upwards with t ht
    exact summable_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] : ‖(3 / 4 : ℝ)‖ < 1)
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    exact integrandTerm_hasSum t

private theorem integral_integrandTerm (n : ℕ) :
    (∫ t in (0 : ℝ)..(Real.pi / 2),
      integrandTerm eccentricity n t) =
      binomialCoefficient n * (-eccentricity ^ 2) ^ n *
        sinePowerIntegral n := by
  unfold integrandTerm
  rw [intervalIntegral.integral_const_mul,
    integral_sin_even_eq_sinePowerIntegral]

private theorem integratedTerm_hasSum :
    HasSum (integratedTerm eccentricity) perimeter := by
  have h := integrandIntegral_hasSum.mul_left (4 * a)
  convert h using 1
  · funext n
    rw [integral_integrandTerm]
    unfold integratedTerm
    ring

private theorem sinePowerIntegral_eq_choose (n : ℕ) :
    sinePowerIntegral n =
      Real.pi / 2 * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n := by
  have hnat :=
    Nat.choose_mul_factorial_mul_factorial
      (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at hnat
  have hfact := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at hfact
  have hpow :
      (2 : ℝ) ^ (2 * n + 1) = 2 * (4 : ℝ) ^ n := by
    rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add, pow_mul]
    norm_num
  unfold sinePowerIntegral
  rw [hpow, ← hfact]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hp : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [hf, hp]

private theorem integratedTerm_eq_normalized (n : ℕ) :
    integratedTerm eccentricity n =
      2 * Real.pi * a * normalizedTerm n := by
  unfold integratedTerm normalizedTerm
  rw [sinePowerIntegral_eq_choose]
  ring

private def centralRatio (n : ℕ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n

private theorem centralRatio_succ (n : ℕ) :
    centralRatio (n + 1) =
      centralRatio n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  have hnat := Nat.succ_mul_centralBinom_succ n
  have hreal := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at hreal
  change
    (Nat.centralBinom (n + 1) : ℝ) / (4 : ℝ) ^ (n + 1) =
      ((Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n) *
        (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))
  rw [pow_succ]
  have hp : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hp, hn]
  nlinarith

private theorem centralRatio_nonneg (n : ℕ) :
    0 ≤ centralRatio n := by
  unfold centralRatio
  positivity

private theorem centralRatio_antitone :
    Antitone centralRatio := by
  apply antitone_nat_of_succ_le
  intro n
  rw [centralRatio_succ]
  have hc := centralRatio_nonneg n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply (div_le_iff₀ (by positivity)).2
  nlinarith

private theorem norm_normalizedTerm (n : ℕ) :
    ‖normalizedTerm n‖ =
      |binomialCoefficient n| * (3 / 4 : ℝ) ^ n *
        centralRatio n := by
  have hchoose :
      |(Nat.choose (2 * n) n : ℝ)| =
        (Nat.choose (2 * n) n : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have hfour :
      |(4 : ℝ) ^ n| = (4 : ℝ) ^ n :=
    abs_of_nonneg (by positivity)
  rw [Real.norm_eq_abs]
  unfold normalizedTerm centralRatio
  rw [eccentricity_sq, abs_div, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4),
    hchoose, hfour]
  ring

private theorem normalizedTerm_norm_succ_le (n : ℕ) :
    ‖normalizedTerm (n + 1)‖ ≤
      (3 / 4 : ℝ) * ‖normalizedTerm n‖ := by
  rw [norm_normalizedTerm, norm_normalizedTerm, pow_succ]
  calc
    |binomialCoefficient (n + 1)| *
          ((3 / 4 : ℝ) ^ n * (3 / 4)) *
          centralRatio (n + 1) =
        (3 / 4 : ℝ) *
          (|binomialCoefficient (n + 1)| *
            (3 / 4 : ℝ) ^ n * centralRatio (n + 1)) := by
      ring
    _ ≤ (3 / 4 : ℝ) *
          (|binomialCoefficient n| *
            (3 / 4 : ℝ) ^ n * centralRatio n) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        |binomialCoefficient (n + 1)| * (3 / 4 : ℝ) ^ n *
            centralRatio (n + 1) ≤
            |binomialCoefficient n| * (3 / 4 : ℝ) ^ n *
              centralRatio (n + 1) := by
          apply mul_le_mul_of_nonneg_right _ (centralRatio_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (binomialCoefficient_abs_succ_le n) (by positivity)
        _ ≤ |binomialCoefficient n| * (3 / 4 : ℝ) ^ n *
              centralRatio n := by
          exact mul_le_mul_of_nonneg_left
            (centralRatio_antitone (Nat.le_succ n))
            (mul_nonneg (abs_nonneg _) (by positivity))

private theorem normalizedTerm_norm_le_geometric (n : ℕ) :
    ‖normalizedTerm n‖ ≤ (3 / 4 : ℝ) ^ n := by
  induction n with
  | zero =>
      norm_num [normalizedTerm, binomialCoefficient, centralRatio]
  | succ n ih =>
      calc
        ‖normalizedTerm (n + 1)‖ ≤
            (3 / 4 : ℝ) * ‖normalizedTerm n‖ :=
          normalizedTerm_norm_succ_le n
        _ ≤ (3 / 4 : ℝ) * (3 / 4 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (3 / 4 : ℝ) ^ (n + 1) := by
          rw [pow_succ]
          ring

private theorem summable_normalizedTerm :
    Summable normalizedTerm := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] : ‖(3 / 4 : ℝ)‖ < 1))
  exact normalizedTerm_norm_le_geometric

private theorem normalizedTailTerm_norm_le (k : ℕ) :
    ‖normalizedTerm (k + 10)‖ ≤
      ‖normalizedTerm 10‖ * (3 / 4 : ℝ) ^ k := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      calc
        ‖normalizedTerm (k + 1 + 10)‖ =
            ‖normalizedTerm ((k + 10) + 1)‖ := by
          congr 2
        _ ≤ (3 / 4 : ℝ) * ‖normalizedTerm (k + 10)‖ :=
          normalizedTerm_norm_succ_le (k + 10)
        _ ≤ (3 / 4 : ℝ) *
            (‖normalizedTerm 10‖ * (3 / 4 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = ‖normalizedTerm 10‖ * (3 / 4 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          ring

private theorem normalizedTailTen_abs_le :
    |∑' k : ℕ, normalizedTerm (k + 10)| ≤
      4 * ‖normalizedTerm 10‖ := by
  have hgeom :
      Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] : ‖(3 / 4 : ℝ)‖ < 1)
  have hmajor :
      Summable (fun k : ℕ =>
        ‖normalizedTerm 10‖ * (3 / 4 : ℝ) ^ k) :=
    hgeom.mul_left _
  have hnorm :
      Summable (fun k : ℕ => ‖normalizedTerm (k + 10)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      normalizedTailTerm_norm_le hmajor
  calc
    |∑' k : ℕ, normalizedTerm (k + 10)| ≤
        ∑' k : ℕ, ‖normalizedTerm (k + 10)‖ := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ,
        ‖normalizedTerm 10‖ * (3 / 4 : ℝ) ^ k :=
      Summable.tsum_le_tsum normalizedTailTerm_norm_le hnorm hmajor
    _ = 4 * ‖normalizedTerm 10‖ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one
        (by norm_num [Real.norm_eq_abs] : ‖(3 / 4 : ℝ)‖ < 1)]
      ring

private theorem normalizedSeries_bounds :
    (∑ n ∈ Finset.range 10, normalizedTerm n) -
          4 * ‖normalizedTerm 10‖ ≤
        ∑' n : ℕ, normalizedTerm n ∧
      (∑' n : ℕ, normalizedTerm n) ≤
        (∑ n ∈ Finset.range 10, normalizedTerm n) +
          4 * ‖normalizedTerm 10‖ := by
  have hsplit := summable_normalizedTerm.sum_add_tsum_nat_add 10
  have htail := normalizedTailTen_abs_le
  rw [abs_le] at htail
  constructor <;> linarith

private theorem perimeter_eq_normalizedSeries :
    perimeter =
      2 * Real.pi * a * ∑' n : ℕ, normalizedTerm n := by
  rw [← integratedTerm_hasSum.tsum_eq, ← tsum_mul_left]
  exact tsum_congr integratedTerm_eq_normalized

private theorem normalizedSeries_decimal_bounds :
    (7708 / 10000 : ℝ) < ∑' n : ℕ, normalizedTerm n ∧
      (∑' n : ℕ, normalizedTerm n) < (7717 / 10000 : ℝ) := by
  rcases normalizedSeries_bounds with ⟨hlo, hhi⟩
  have hcalcLo :
      (7708 / 10000 : ℝ) <
        (∑ n ∈ Finset.range 10, normalizedTerm n) -
          4 * ‖normalizedTerm 10‖ := by
    norm_num [normalizedTerm, binomialCoefficient, eccentricity_sq,
      Finset.sum_range_succ, Finset.prod_range_succ, Nat.choose,
      Real.norm_eq_abs]
  have hcalcHi :
      (∑ n ∈ Finset.range 10, normalizedTerm n) +
          4 * ‖normalizedTerm 10‖ <
        (7717 / 10000 : ℝ) := by
    norm_num [normalizedTerm, binomialCoefficient, eccentricity_sq,
      Finset.sum_range_succ, Finset.prod_range_succ, Nat.choose,
      Real.norm_eq_abs]
  exact ⟨hcalcLo.trans_le hlo, hhi.trans_lt hcalcHi⟩

private theorem perimeter_decimal_bounds :
    (484 / 100 : ℝ) < perimeter ∧
      perimeter < (485 / 100 : ℝ) := by
  rcases normalizedSeries_decimal_bounds with ⟨hlo, hhi⟩
  have hfactor : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hmulLo := mul_lt_mul_of_pos_left hlo hfactor
  have hmulHi := mul_lt_mul_of_pos_left hhi hfactor
  rw [perimeter_eq_normalizedSeries]
  norm_num [a]
  constructor
  · nlinarith [Real.pi_gt_d20]
  · nlinarith [Real.pi_lt_d20]

private theorem roughFourTerm_decimal_bounds :
    (486 / 100 : ℝ) < roughFourTerm ∧
      roughFourTerm < (487 / 100 : ℝ) := by
  unfold roughFourTerm
  constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem gap1 :
    ∀ t : ℝ, x t = a * Real.sin t := by
  intro t
  rfl

theorem gap2 :
    ∀ t : ℝ, y t = b * Real.cos t := by
  intro t
  rfl

theorem gap3 :
    ∀ t : ℝ,
      Real.sqrt (deriv x t ^ 2 + deriv y t ^ 2) = speed t := by
  intro t
  rfl

theorem gap4 :
    ∀ t : ℝ,
      speed t =
        Real.sqrt (a ^ 2 * Real.cos t ^ 2 +
          b ^ 2 * Real.sin t ^ 2) := by
  intro t
  unfold speed
  rw [deriv_x, deriv_y]
  ring_nf

theorem gap5 :
    ∃ e : ℝ, e = eccentricity ∧
      ∀ t : ℝ,
        Real.sqrt (a ^ 2 * Real.cos t ^ 2 +
            b ^ 2 * Real.sin t ^ 2) =
          a * Real.sqrt (1 - e ^ 2 * Real.sin t ^ 2) := by
  refine ⟨eccentricity, rfl, ?_⟩
  intro t
  rw [eccentricity_sq]
  unfold a b
  norm_num
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem gap6 :
    ∃ e : ℝ, e = eccentricity ∧
      ∀ t : ℝ,
        speed t =
          a * Real.sqrt (1 - e ^ 2 * Real.sin t ^ 2) := by
  obtain ⟨e, he, hshape⟩ := gap5
  refine ⟨e, he, ?_⟩
  intro t
  rw [gap4]
  exact hshape t

theorem gap7 :
    ∃ e : ℝ, e = Real.sqrt (a ^ 2 - b ^ 2) / a := by
  exact ⟨eccentricity, rfl⟩

theorem gap8 :
    ∃ e : ℝ, e = eccentricity ∧
      perimeter =
        4 * a * ∫ t in (0 : ℝ)..(Real.pi / 2),
          Real.sqrt (1 - e ^ 2 * Real.sin t ^ 2) := by
  exact ⟨eccentricity, rfl, rfl⟩

theorem gap9 :
    ∃ e : ℝ, e = eccentricity ∧
      perimeter =
        4 * a * ∫ t in (0 : ℝ)..(Real.pi / 2),
          ∑' n : ℕ, integrandTerm e n t := by
  refine ⟨eccentricity, rfl, ?_⟩
  unfold perimeter
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact (integrandTerm_hasSum t).tsum_eq.symm

theorem gap10 :
    ∃ e : ℝ, e = eccentricity ∧
      perimeter = ∑' n : ℕ, integratedTerm e n := by
  exact ⟨eccentricity, rfl, integratedTerm_hasSum.tsum_eq.symm⟩

theorem gap11 :
    0 < approximationError := by
  unfold approximationError
  exact abs_pos.mpr
    (sub_ne_zero.mpr (ne_of_gt perimeter_decimal_bounds.1))

theorem gap12 :
    approximationError < (1 / 100 : ℝ) := by
  unfold approximationError
  rw [abs_of_pos (sub_pos.mpr perimeter_decimal_bounds.1)]
  linarith [perimeter_decimal_bounds.2]

theorem gap13 :
    (0 : ℝ) < 1 / 100 := by
  norm_num

theorem gap14 :
    perimeter =
      2 * Real.pi * a * ∑' n : ℕ, normalizedTerm n := by
  exact perimeter_eq_normalizedSeries

theorem gap15 :
    Approx perimeter roughFourTerm (3 / 100 : ℝ) := by
  rw [Approx, abs_lt]
  rcases perimeter_decimal_bounds with ⟨hpLo, hpHi⟩
  rcases roughFourTerm_decimal_bounds with ⟨hrLo, hrHi⟩
  constructor <;> linarith

theorem gap16 :
    Approx roughFourTerm (484 / 100 : ℝ) (3 / 100 : ℝ) := by
  rw [Approx, abs_lt]
  rcases roughFourTerm_decimal_bounds with ⟨hrLo, hrHi⟩
  constructor <;> linarith

theorem gap17 :
    Approx perimeter (484 / 100 : ℝ) (1 / 100 : ℝ) := by
  simpa [Approx, approximationError] using gap12

end

end ProofGap.Exercise2934
