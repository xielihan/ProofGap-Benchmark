import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3096

noncomputable section

open Filter
open scoped BigOperators Topology

def positiveFactor (n : ℕ) : ℝ :=
  1 + 1 / Real.sqrt n

def leftNegativeFactor (n : ℕ) : ℝ :=
  1 - 1 / Real.sqrt (4 * n - 1)

def rightNegativeFactor (n : ℕ) : ℝ :=
  1 - 1 / Real.sqrt (4 * n + 1)

def groupFactor (n : ℕ) : ℝ :=
  positiveFactor n * leftNegativeFactor n * rightNegativeFactor n

def u (n : ℕ) : ℝ :=
  Real.log (groupFactor n)

def alpha (n : ℕ) : ℝ :=
  groupFactor n - 1

def mainAlpha (n : ℕ) : ℝ :=
  -3 / Real.sqrt (16 * (n : ℝ) ^ 2 - 1)

def comparisonTerm (n : ℕ) : ℝ :=
  1 / Real.rpow (n : ℝ) (3 / 2 : ℝ)

def flattenedFactor (k : ℕ) : ℝ :=
  if k % 3 = 0 then positiveFactor (k / 3 + 1)
  else if k % 3 = 1 then leftNegativeFactor (k / 3 + 1)
  else rightNegativeFactor (k / 3 + 1)

def q (n : ℕ) : ℝ :=
  if n = 0 then 1 else flattenedFactor (n - 1)

def qLogPartialSum (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (3 * m), Real.log (q j)

def groupedPartialSum (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, u n

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))


private theorem positiveFactor_pos (n : ℕ) :
    0 < positiveFactor n := by
  unfold positiveFactor
  positivity

private theorem leftNegativeFactor_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < leftNegativeFactor n := by
  unfold leftNegativeFactor
  let b := Real.sqrt (4 * (n : ℝ) - 1)
  have hb : 0 < b := Real.sqrt_pos.2 (by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  have hb_sq : b ^ 2 = 4 * (n : ℝ) - 1 := by
    dsimp [b]
    apply Real.sq_sqrt
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have harg : (3 : ℝ) ≤ 4 * (n : ℝ) - 1 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hb_one : 1 < b := by nlinarith
  change 0 < 1 - 1 / Real.sqrt (4 * (n : ℝ) - 1)
  change 0 < 1 - 1 / b
  have : 1 / b < 1 := (div_lt_one hb).2 (by linarith)
  linarith

private theorem rightNegativeFactor_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < rightNegativeFactor n := by
  unfold rightNegativeFactor
  let b := Real.sqrt (4 * (n : ℝ) + 1)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hb_sq : b ^ 2 = 4 * (n : ℝ) + 1 := by
    dsimp [b]
    exact Real.sq_sqrt (by positivity)
  have harg : (5 : ℝ) ≤ 4 * (n : ℝ) + 1 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hb_one : 1 < b := by nlinarith
  change 0 < 1 - 1 / Real.sqrt (4 * (n : ℝ) + 1)
  change 0 < 1 - 1 / b
  have : 1 / b < 1 := (div_lt_one hb).2 (by linarith)
  linarith

private theorem groupFactor_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < groupFactor n := by
  unfold groupFactor
  exact mul_pos
    (mul_pos (positiveFactor_pos n) (leftNegativeFactor_pos n hn))
    (rightNegativeFactor_pos n hn)

private theorem u_eq_log_sum (n : ℕ) (hn : 1 ≤ n) :
    u n =
      Real.log (positiveFactor n) +
        Real.log (leftNegativeFactor n) +
          Real.log (rightNegativeFactor n) := by
  unfold u groupFactor
  rw [Real.log_mul (mul_ne_zero
      (positiveFactor_pos n).ne' (leftNegativeFactor_pos n hn).ne')
    (rightNegativeFactor_pos n hn).ne',
    Real.log_mul (positiveFactor_pos n).ne'
      (leftNegativeFactor_pos n hn).ne']

private theorem q_three_one (m : ℕ) :
    q (3 * m + 1) = positiveFactor (m + 1) := by
  simp [q, flattenedFactor]

private theorem q_three_two (m : ℕ) :
    q (3 * m + 2) = leftNegativeFactor (m + 1) := by
  simp [q, flattenedFactor]
  congr 1
  omega

private theorem q_three_three (m : ℕ) :
    q (3 * m + 3) = rightNegativeFactor (m + 1) := by
  simp [q, flattenedFactor]
  congr 1
  omega

private theorem grouped_sum_identity (m : ℕ) :
    qLogPartialSum m = groupedPartialSum m := by
  induction m with
  | zero =>
      simp [qLogPartialSum, groupedPartialSum]
  | succ m ih =>
      unfold qLogPartialSum groupedPartialSum
      rw [show 3 * (m + 1) = 3 * m + 3 by omega,
        Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      change qLogPartialSum m +
          Real.log (q (3 * m + 1)) +
          Real.log (q (3 * m + 2)) +
          Real.log (q (3 * m + 3)) =
        groupedPartialSum m + u (m + 1)
      rw [ih, q_three_one, q_three_two, q_three_three,
        u_eq_log_sum (m + 1) (by omega)]
      ring

private theorem reciprocal_sqrt_nat_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hs :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [one_div] using tendsto_inv_atTop_zero.comp hs

private theorem left_argument_tendsto_atTop :
    Tendsto (fun n : ℕ => 4 * (n : ℝ) - 1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop ((b + 1) / 4))
  ] with n hn
  linarith

private theorem right_argument_tendsto_atTop :
    Tendsto (fun n : ℕ => 4 * (n : ℝ) + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop ((b - 1) / 4))
  ] with n hn
  linarith

private theorem reciprocal_sqrt_left_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / Real.sqrt (4 * (n : ℝ) - 1))
      atTop (𝓝 0) := by
  have hs :=
    Real.tendsto_sqrt_atTop.comp left_argument_tendsto_atTop
  simpa only [one_div] using tendsto_inv_atTop_zero.comp hs

private theorem reciprocal_sqrt_right_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / Real.sqrt (4 * (n : ℝ) + 1))
      atTop (𝓝 0) := by
  have hs :=
    Real.tendsto_sqrt_atTop.comp right_argument_tendsto_atTop
  simpa only [one_div] using tendsto_inv_atTop_zero.comp hs

private theorem alpha_tendsto_zero :
    Tendsto alpha atTop (𝓝 0) := by
  have hp :
      Tendsto positiveFactor atTop (𝓝 1) := by
    unfold positiveFactor
    simpa using tendsto_const_nhds.add reciprocal_sqrt_nat_tendsto_zero
  have hl :
      Tendsto leftNegativeFactor atTop (𝓝 1) := by
    unfold leftNegativeFactor
    simpa using tendsto_const_nhds.sub reciprocal_sqrt_left_tendsto_zero
  have hr :
      Tendsto rightNegativeFactor atTop (𝓝 1) := by
    unfold rightNegativeFactor
    simpa using tendsto_const_nhds.sub reciprocal_sqrt_right_tendsto_zero
  have h1 :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  unfold alpha groupFactor
  simpa using ((hp.mul hl).mul hr).sub h1

private theorem alpha_neg (n : ℕ) (hn : 1 ≤ n) :
    alpha n < 0 := by
  let a := Real.sqrt (n : ℝ)
  let b := Real.sqrt (4 * (n : ℝ) - 1)
  let c := Real.sqrt (4 * (n : ℝ) + 1)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by
    linarith)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have ha_sq : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hb_sq : b ^ 2 = 4 * (n : ℝ) - 1 := by
    dsimp [b]
    exact Real.sq_sqrt (by linarith)
  have hc_sq : c ^ 2 = 4 * (n : ℝ) + 1 := by
    dsimp [c]
    exact Real.sq_sqrt (by positivity)
  have ha_one : 1 ≤ a := by nlinarith
  have hb_le : b ≤ 2 * a := by nlinarith
  have hc_lt : c < 2 * a + 1 := by nlinarith
  have hc_gt : a + 1 < c := by nlinarith
  have hb_gt : a < b := by nlinarith
  have hsum : 2 * a + 1 < b + c := by nlinarith
  have hmul :
      2 * a * (a - c) ≤ b * (a - c) := by
    exact mul_le_mul_of_nonpos_right hb_le (by nlinarith)
  have hac : a * c < a * (2 * a + 1) :=
    mul_lt_mul_of_pos_left hc_lt ha
  have hD :
      0 < a * b + a * c - b * c + b + c - a - 1 := by
    nlinarith
  unfold alpha groupFactor positiveFactor leftNegativeFactor
    rightNegativeFactor
  change
    (1 + 1 / a) * (1 - 1 / b) * (1 - 1 / c) - 1 < 0
  field_simp [ha.ne', hb.ne', hc.ne']
  nlinarith

private def invSqrt (n : ℕ) : ℝ :=
  1 / Real.sqrt (n : ℝ)

private def leftCorrection (n : ℕ) : ℝ :=
  1 / Real.sqrt (4 * (n : ℝ) - 1) - invSqrt n / 2

private def rightCorrection (n : ℕ) : ℝ :=
  1 / Real.sqrt (4 * (n : ℝ) + 1) - invSqrt n / 2

private def quadraticAlpha (n : ℕ) : ℝ :=
  -(3 / 4 : ℝ) * (invSqrt n) ^ 2

private theorem comparisonTerm_eq_invSqrt_cube
    (n : ℕ) (hn : 1 ≤ n) :
    comparisonTerm n = (invSqrt n) ^ 3 := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  unfold comparisonTerm invSqrt
  rw [div_pow]
  norm_num only [one_pow]
  apply congrArg (fun z : ℝ => 1 / z)
  rw [Real.sqrt_eq_rpow]
  have hmul := Real.rpow_mul hn0 (1 / 2 : ℝ) (3 : ℝ)
  convert hmul using 1 <;> norm_num

private theorem leftCorrection_formula (n : ℕ) (hn : 1 ≤ n) :
    leftCorrection n =
      1 / (2 * Real.sqrt n * Real.sqrt (4 * (n : ℝ) - 1) *
        (2 * Real.sqrt n + Real.sqrt (4 * (n : ℝ) - 1))) := by
  let a := Real.sqrt (n : ℝ)
  let b := Real.sqrt (4 * (n : ℝ) - 1)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have hab : 0 < 2 * a + b := by positivity
  have ha_sq : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hb_sq : b ^ 2 = 4 * (n : ℝ) - 1 := by
    dsimp [b]
    exact Real.sq_sqrt (by linarith)
  unfold leftCorrection invSqrt
  change 1 / b - (1 / a) / 2 = 1 / (2 * a * b * (2 * a + b))
  field_simp [ha.ne', hb.ne', hab.ne']
  nlinarith

private theorem rightCorrection_formula (n : ℕ) (hn : 1 ≤ n) :
    rightCorrection n =
      -1 / (2 * Real.sqrt n * Real.sqrt (4 * (n : ℝ) + 1) *
        (2 * Real.sqrt n + Real.sqrt (4 * (n : ℝ) + 1))) := by
  let a := Real.sqrt (n : ℝ)
  let c := Real.sqrt (4 * (n : ℝ) + 1)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hac : 0 < 2 * a + c := by positivity
  have ha_sq : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hc_sq : c ^ 2 = 4 * (n : ℝ) + 1 := by
    dsimp [c]
    exact Real.sq_sqrt (by positivity)
  unfold rightCorrection invSqrt
  change 1 / c - (1 / a) / 2 = -1 / (2 * a * c * (2 * a + c))
  field_simp [ha.ne', hc.ne', hac.ne']
  nlinarith

private theorem abs_leftCorrection_le (n : ℕ) (hn : 1 ≤ n) :
    |leftCorrection n| ≤ comparisonTerm n := by
  let a := Real.sqrt (n : ℝ)
  let b := Real.sqrt (4 * (n : ℝ) - 1)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have ha_sq : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hb_sq : b ^ 2 = 4 * (n : ℝ) - 1 := by
    dsimp [b]
    exact Real.sq_sqrt (by linarith)
  have hab : a ≤ b := by nlinarith
  have hden : 0 < 2 * a * b * (2 * a + b) := by positivity
  have hden_lower : a ^ 3 ≤ 2 * a * b * (2 * a + b) := by
    calc
      a ^ 3 = a * a * a := by ring
      _ ≤ 2 * a * b * (2 * a + b) := by
        gcongr <;> nlinarith
  rw [leftCorrection_formula n hn, abs_of_pos (one_div_pos.mpr hden),
    comparisonTerm_eq_invSqrt_cube n hn]
  unfold invSqrt
  rw [div_pow]
  norm_num only [one_pow]
  exact (div_le_div_iff₀ hden (pow_pos ha 3)).2 (by simpa using hden_lower)

private theorem abs_rightCorrection_le (n : ℕ) (hn : 1 ≤ n) :
    |rightCorrection n| ≤ comparisonTerm n := by
  let a := Real.sqrt (n : ℝ)
  let c := Real.sqrt (4 * (n : ℝ) + 1)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have ha_sq : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hc_sq : c ^ 2 = 4 * (n : ℝ) + 1 := by
    dsimp [c]
    exact Real.sq_sqrt (by positivity)
  have hac : a ≤ c := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hden : 0 < 2 * a * c * (2 * a + c) := by positivity
  have hden_lower : a ^ 3 ≤ 2 * a * c * (2 * a + c) := by
    calc
      a ^ 3 = a * a * a := by ring
      _ ≤ 2 * a * c * (2 * a + c) := by
        gcongr <;> nlinarith
  rw [rightCorrection_formula n hn]
  change |-1 / (2 * a * c * (2 * a + c))| ≤ comparisonTerm n
  rw [abs_of_neg (div_neg_of_neg_of_pos (by norm_num) hden),
    comparisonTerm_eq_invSqrt_cube n hn]
  simp only [neg_div, neg_neg]
  unfold invSqrt
  rw [div_pow]
  norm_num only [one_pow]
  exact (div_le_div_iff₀ hden (pow_pos ha 3)).2 (by simpa using hden_lower)

private theorem alpha_minus_quadratic_formula (n : ℕ) (_hn : 1 ≤ n) :
    alpha n - quadraticAlpha n =
      (invSqrt n) ^ 3 / 4 +
        (1 + invSqrt n) * (invSqrt n / 2 - 1) *
          (leftCorrection n + rightCorrection n) +
        (1 + invSqrt n) * leftCorrection n * rightCorrection n := by
  have hl :
      1 / Real.sqrt (4 * (n : ℝ) - 1) =
        invSqrt n / 2 + leftCorrection n := by
    unfold leftCorrection
    ring
  have hr :
      1 / Real.sqrt (4 * (n : ℝ) + 1) =
        invSqrt n / 2 + rightCorrection n := by
    unfold rightCorrection
    ring
  unfold alpha groupFactor positiveFactor leftNegativeFactor
    rightNegativeFactor quadraticAlpha
  change
    (1 + invSqrt n) *
        (1 - 1 / Real.sqrt (4 * (n : ℝ) - 1)) *
        (1 - 1 / Real.sqrt (4 * (n : ℝ) + 1)) -
      1 - (-(3 / 4) * invSqrt n ^ 2) =
      invSqrt n ^ 3 / 4 +
        (1 + invSqrt n) * (invSqrt n / 2 - 1) *
          (leftCorrection n + rightCorrection n) +
        (1 + invSqrt n) * leftCorrection n * rightCorrection n
  rw [hl, hr]
  ring

private theorem abs_alpha_minus_quadratic_le (n : ℕ) (hn : 1 ≤ n) :
    |alpha n - quadraticAlpha n| ≤ 7 * comparisonTerm n := by
  let t := invSqrt n
  let l := leftCorrection n
  let r := rightCorrection n
  let c := comparisonTerm n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hnR
  have ht : 0 < t := by
    dsimp [t, invSqrt]
    positivity
  have ht_le : t ≤ 1 := by
    dsimp [t, invSqrt]
    exact (div_le_one (Real.sqrt_pos.2 (by positivity))).2 hsqrt
  have hc_eq : c = t ^ 3 := by
    dsimp [c, t]
    exact comparisonTerm_eq_invSqrt_cube n hn
  have hc0 : 0 ≤ c := by rw [hc_eq]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc_eq]
    exact pow_le_one₀ ht.le ht_le
  have hl : |l| ≤ c := by
    dsimp [l, c]
    exact abs_leftCorrection_le n hn
  have hr : |r| ≤ c := by
    dsimp [r, c]
    exact abs_rightCorrection_le n hn
  have hA : |t ^ 3 / 4| ≤ c := by
    rw [abs_div, abs_pow, abs_of_pos ht]
    norm_num
    rw [← hc_eq]
    linarith
  have hB :
      |(1 + t) * (t / 2 - 1) * (l + r)| ≤ 4 * c := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + t),
      abs_of_nonpos (by linarith : t / 2 - 1 ≤ 0)]
    rw [show -(t / 2 - 1) = 1 - t / 2 by ring]
    have hfac0 : 0 ≤ 1 - t / 2 := by linarith
    have hfac : (1 + t) * (1 - t / 2) ≤ 2 := by
      calc
        (1 + t) * (1 - t / 2) ≤ 2 * (1 - t / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hfac0
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        _ = 2 := by ring
    have hsum : |l + r| ≤ 2 * c := by
      linarith [abs_add_le l r]
    calc
      (1 + t) * (1 - t / 2) * |l + r| ≤
          2 * |l + r| :=
        mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
      _ ≤ 2 * (2 * c) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 4 * c := by ring
  have hC :
      |(1 + t) * l * r| ≤ 2 * c := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + t)]
    have hfirst : (1 + t) * |l| ≤ 2 * c := by
      exact mul_le_mul (by linarith) hl (abs_nonneg _) (by linarith)
    calc
      (1 + t) * |l| * |r| ≤ 2 * c * |r| :=
        mul_le_mul_of_nonneg_right hfirst (abs_nonneg _)
      _ ≤ 2 * c * c :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ 2 * c := by nlinarith
  rw [alpha_minus_quadratic_formula n hn]
  change |t ^ 3 / 4 + (1 + t) * (t / 2 - 1) * (l + r) +
      (1 + t) * l * r| ≤ 7 * c
  calc
    |t ^ 3 / 4 + (1 + t) * (t / 2 - 1) * (l + r) +
        (1 + t) * l * r| ≤
        (|t ^ 3 / 4| + |(1 + t) * (t / 2 - 1) * (l + r)|) +
          |(1 + t) * l * r| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ (c + 4 * c) + 2 * c := add_le_add (add_le_add hA hB) hC
    _ = 7 * c := by ring

private theorem main_minus_quadratic_formula (n : ℕ) (hn : 1 ≤ n) :
    mainAlpha n - quadraticAlpha n =
      -3 / (4 * (n : ℝ) * Real.sqrt (16 * (n : ℝ) ^ 2 - 1) *
        (4 * (n : ℝ) + Real.sqrt (16 * (n : ℝ) ^ 2 - 1))) := by
  let x := (n : ℝ)
  let a := Real.sqrt x
  let d := Real.sqrt (16 * x ^ 2 - 1)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have ha : 0 < a := Real.sqrt_pos.2 hx
  have hd : 0 < d := Real.sqrt_pos.2 (by
    have hx1 : (1 : ℝ) ≤ x := by
      dsimp [x]
      exact_mod_cast hn
    nlinarith [sq_nonneg (x - 1)])
  have harg : 0 ≤ 16 * x ^ 2 - 1 := by
    have hx1 : (1 : ℝ) ≤ x := by
      dsimp [x]
      exact_mod_cast hn
    nlinarith [sq_nonneg (x - 1)]
  have hsum : 0 < 4 * x + d := by positivity
  have ha_sq : a ^ 2 = x := by
    dsimp [a]
    exact Real.sq_sqrt hx.le
  have hd_sq : d ^ 2 = 16 * x ^ 2 - 1 := by
    dsimp [d]
    exact Real.sq_sqrt harg
  have hinv_sq : (1 / a) ^ 2 = 1 / x := by
    field_simp [ha.ne', hx.ne']
    nlinarith
  unfold mainAlpha quadraticAlpha invSqrt
  change
    -3 / d - (-(3 / 4) * (1 / a) ^ 2) =
      -3 / (4 * x * d * (4 * x + d))
  rw [hinv_sq]
  field_simp [hx.ne', ha.ne', hd.ne', hsum.ne']
  nlinarith [hd_sq]

private theorem abs_main_minus_quadratic_le (n : ℕ) (hn : 1 ≤ n) :
    |mainAlpha n - quadraticAlpha n| ≤ comparisonTerm n := by
  let x := (n : ℝ)
  let a := Real.sqrt x
  let d := Real.sqrt (16 * x ^ 2 - 1)
  have hx1 : (1 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hn
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have ha : 0 < a := Real.sqrt_pos.2 hx
  have hd : 0 < d := Real.sqrt_pos.2 (by
    nlinarith [sq_nonneg (x - 1)])
  have harg : 0 ≤ 16 * x ^ 2 - 1 := by
    nlinarith [sq_nonneg (x - 1)]
  have ha_sq : a ^ 2 = x := by
    dsimp [a]
    exact Real.sq_sqrt hx.le
  have hd_sq : d ^ 2 = 16 * x ^ 2 - 1 := by
    dsimp [d]
    exact Real.sq_sqrt harg
  have ha_one : 1 ≤ a := by nlinarith
  have hax : a ≤ x := by nlinarith
  have hd3 : 3 * x ≤ d := by nlinarith [sq_nonneg (x - 1)]
  have hden : 0 < 4 * x * d * (4 * x + d) := by positivity
  have hden_lower : 3 * a ^ 3 ≤ 4 * x * d * (4 * x + d) := by
    calc
      3 * a ^ 3 = (3 * a) * a * a := by ring
      _ ≤ (4 * x) * d * (4 * x + d) := by
        gcongr <;> nlinarith
  rw [main_minus_quadratic_formula n hn]
  change |-3 / (4 * x * d * (4 * x + d))| ≤ comparisonTerm n
  rw [abs_of_neg (div_neg_of_neg_of_pos (by norm_num) hden),
    comparisonTerm_eq_invSqrt_cube n hn]
  simp only [neg_div, neg_neg]
  unfold invSqrt
  change 3 / (4 * x * d * (4 * x + d)) ≤ (1 / a) ^ 3
  rw [div_pow]
  norm_num only [one_pow]
  exact (div_le_div_iff₀ hden (pow_pos ha 3)).2 (by simpa using hden_lower)

private theorem alpha_minus_main_isBigO :
    (fun n => alpha n - mainAlpha n) =O[atTop] comparisonTerm := by
  refine Asymptotics.IsBigO.of_bound 8 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  change |alpha n - mainAlpha n| ≤ 8 * |comparisonTerm n|
  have hc : 0 ≤ comparisonTerm n := by
    unfold comparisonTerm
    exact div_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
  rw [abs_of_nonneg hc]
  have ha := abs_alpha_minus_quadratic_le n hn
  have hm := abs_main_minus_quadratic_le n hn
  rw [show alpha n - mainAlpha n =
    (alpha n - quadraticAlpha n) +
      -(mainAlpha n - quadraticAlpha n) by ring]
  calc
    |(alpha n - quadraticAlpha n) +
        -(mainAlpha n - quadraticAlpha n)| ≤
        |alpha n - quadraticAlpha n| +
          |-(mainAlpha n - quadraticAlpha n)| := abs_add_le _ _
    _ = |alpha n - quadraticAlpha n| +
          |mainAlpha n - quadraticAlpha n| := by rw [abs_neg]
    _ ≤ 7 * comparisonTerm n + comparisonTerm n := add_le_add ha hm
    _ = 8 * comparisonTerm n := by ring

private theorem comparison_tendsto_zero :
    Tendsto comparisonTerm atTop (𝓝 0) := by
  have h :
      Tendsto (fun n : ℕ => (invSqrt n) ^ 3) atTop (𝓝 0) := by
    simpa only [invSqrt, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] using
      reciprocal_sqrt_nat_tendsto_zero.pow 3
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (comparisonTerm_eq_invSqrt_cube n hn).symm

private theorem main_argument_tendsto_atTop :
    Tendsto (fun n : ℕ => 16 * (n : ℝ) ^ 2 - 1) atTop atTop := by
  have hsquare :
      Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hmul :
      Tendsto (fun n : ℕ => 16 * (n : ℝ) ^ 2) atTop atTop :=
    hsquare.const_mul_atTop (by norm_num)
  simpa [sub_eq_add_neg] using
    tendsto_atTop_add_const_right atTop (-1 : ℝ) hmul

private theorem mainAlpha_tendsto_zero :
    Tendsto mainAlpha atTop (𝓝 0) := by
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (16 * (n : ℝ) ^ 2 - 1))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp main_argument_tendsto_atTop
  have hinv :
      Tendsto
        (fun n : ℕ => (Real.sqrt (16 * (n : ℝ) ^ 2 - 1))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  unfold mainAlpha
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv :
      Tendsto
        (fun n : ℕ => (-3 : ℝ) *
          (Real.sqrt (16 * (n : ℝ) ^ 2 - 1))⁻¹)
        atTop (𝓝 ((-3 : ℝ) * 0)))

private def ratioError (n : ℕ) : ℝ :=
  (alpha n - mainAlpha n) / (1 + mainAlpha n)

private theorem ratioError_tendsto_zero :
    Tendsto ratioError atTop (𝓝 0) := by
  have hden :
      Tendsto (fun n => 1 + mainAlpha n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add mainAlpha_tendsto_zero
  have hinv :
      Tendsto (fun n => (1 + mainAlpha n)⁻¹) atTop (𝓝 1) := by
    simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hnum :
      Tendsto (fun n => alpha n - mainAlpha n) atTop (𝓝 0) := by
    simpa using alpha_tendsto_zero.sub mainAlpha_tendsto_zero
  unfold ratioError
  simpa [div_eq_mul_inv] using hnum.mul hinv

private theorem ratioError_isBigO :
    ratioError =O[atTop] comparisonTerm := by
  have hden :
      Tendsto (fun n => 1 + mainAlpha n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add mainAlpha_tendsto_zero
  have hinv :
      Tendsto (fun n => (1 + mainAlpha n)⁻¹) atTop (𝓝 1) := by
    simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hmul := alpha_minus_main_isBigO.mul (hinv.isBigO_one ℝ)
  simpa [ratioError, div_eq_mul_inv] using hmul

private theorem log_one_add_isEquivalent :
    Asymptotics.IsEquivalent (𝓝 0)
      (fun x : ℝ => Real.log (1 + x)) (fun x : ℝ => x) := by
  have hinner :
      HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).const_add 1
  have houter :
      HasDerivAt Real.log 1 ((fun x : ℝ => 1 + x) 0) := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hderiv :
      HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    simpa [Function.comp_def] using houter.comp 0 hinner
  have hlo :
      (fun x : ℝ => Real.log (1 + x) - x) =o[𝓝 0]
        (fun x : ℝ => x) := by
    simpa using hderiv.isLittleO
  exact hlo.isEquivalent

private theorem log_ratioError_isBigO :
    (fun n => Real.log (1 + ratioError n)) =O[atTop] comparisonTerm := by
  have hlog :
      (fun n => Real.log (1 + ratioError n)) =O[atTop] ratioError := by
    simpa [Function.comp_def] using
      log_one_add_isEquivalent.isBigO.comp_tendsto ratioError_tendsto_zero
  exact hlog.trans ratioError_isBigO

private theorem main_base_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < 1 + mainAlpha n := by
  let x := (n : ℝ)
  let d := Real.sqrt (16 * x ^ 2 - 1)
  have hx1 : (1 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hn
  have hd : 0 < d := Real.sqrt_pos.2 (by
    nlinarith [sq_nonneg (x - 1)])
  have hd_sq : d ^ 2 = 16 * x ^ 2 - 1 := by
    dsimp [d]
    exact Real.sq_sqrt (by
      nlinarith [sq_nonneg (x - 1)])
  have hd3 : 3 < d := by
    nlinarith [sq_nonneg (x - 1)]
  unfold mainAlpha
  change 0 < 1 + -3 / d
  have hdiv : 3 / d < 1 := (div_lt_one hd).2 hd3
  rw [show (-3 : ℝ) / d = -(3 / d) by ring]
  exact sub_pos.mpr hdiv

private theorem log_difference_eq_log_ratioError (n : ℕ) (hn : 1 ≤ n) :
    u n - Real.log (1 + mainAlpha n) =
      Real.log (1 + ratioError n) := by
  have hg := groupFactor_pos n hn
  have hm := main_base_pos n hn
  have hratio :
      1 + ratioError n = groupFactor n / (1 + mainAlpha n) := by
    unfold ratioError alpha
    field_simp [hm.ne']
    ring
  rw [hratio, Real.log_div hg.ne' hm.ne']
  rfl

private theorem logarithmic_remainder_isBigO :
    (fun n => u n - Real.log (1 + mainAlpha n)) =O[atTop]
      comparisonTerm := by
  apply log_ratioError_isBigO.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (log_difference_eq_log_ratioError n hn).symm
  · exact Eventually.of_forall fun _ => rfl

private theorem comparison_summable :
    Summable comparisonTerm := by
  unfold comparisonTerm
  exact Real.summable_one_div_nat_rpow.mpr (by norm_num)

private theorem logarithmic_remainder_summable :
    Summable (fun n => u n - Real.log (1 + mainAlpha n)) :=
  summable_of_isBigO_nat comparison_summable logarithmic_remainder_isBigO

private theorem log_main_not_summable :
    ¬Summable (fun n => Real.log (1 + mainAlpha n)) := by
  intro hlog
  have hscaled :
      Summable (fun n => 2 * |Real.log (1 + mainAlpha n)|) :=
    hlog.abs.mul_left 2
  apply Real.not_summable_one_div_natCast
  apply Summable.of_norm_bounded hscaled
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [mainAlpha]
  · have hn : 1 ≤ n := by omega
    let x := (n : ℝ)
    let d := Real.sqrt (16 * x ^ 2 - 1)
    have hx1 : (1 : ℝ) ≤ x := by
      dsimp [x]
      exact_mod_cast hn
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hd : 0 < d := Real.sqrt_pos.2 (by
      nlinarith [sq_nonneg (x - 1)])
    have hd_sq : d ^ 2 = 16 * x ^ 2 - 1 := by
      dsimp [d]
      exact Real.sq_sqrt (by
        nlinarith [sq_nonneg (x - 1)])
    have hd_le : d ≤ 4 * x := by nlinarith
    have hm : 0 < 1 + mainAlpha n := main_base_pos n hn
    have hlogle :
        Real.log (1 + mainAlpha n) ≤ mainAlpha n := by
      have h := Real.log_le_sub_one_of_pos hm
      linarith
    have hmain : mainAlpha n = -3 / d := by rfl
    have hlogneg : Real.log (1 + mainAlpha n) < 0 := by
      have hmainneg : mainAlpha n < 0 := by
        rw [hmain]
        exact div_neg_of_neg_of_pos (by norm_num) hd
      exact lt_of_le_of_lt hlogle hmainneg
    have hfrac : 3 / (4 * x) ≤ 3 / d := by
      exact (div_le_div_iff₀ (by positivity : 0 < 4 * x) hd).2 (by
        nlinarith)
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hx),
      abs_of_neg hlogneg]
    rw [hmain] at hlogle
    rw [hmain]
    have hscale : 3 / (4 * x) = (3 / 4) * (1 / x) := by
      field_simp [hx.ne']
    rw [hscale] at hfrac
    rw [show (-3 : ℝ) / d = -(3 / d) by ring] at hlogle ⊢
    nlinarith [one_div_pos.mpr hx]

private theorem u_not_summable_from_one :
    ¬SummableFromOne u := by
  intro hu
  have huAll : Summable u :=
    (summable_nat_add_iff 1).mp hu
  have hmain :
      Summable (fun n => Real.log (1 + mainAlpha n)) := by
    have h := huAll.sub logarithmic_remainder_summable
    apply h.congr
    intro n
    ring
  exact log_main_not_summable hmain

private theorem alpha_not_summable_from_one :
    ¬SummableFromOne alpha := by
  intro ha
  have hlog :=
    Real.summable_log_one_add_of_summable ha
  apply u_not_summable_from_one
  apply hlog.congr
  intro k
  unfold u alpha
  congr 1
  ring

private theorem q_log_not_summable_from_one :
    ¬SummableFromOne (fun n => Real.log (q n)) := by
  intro hq
  have h0 :
      Summable (fun k => Real.log (q (3 * k + 1))) := by
    have h := hq.comp_injective
      (show Function.Injective (fun k : ℕ => 3 * k) by
        intro a b hab
        exact mul_left_cancel₀ (by norm_num : (3 : ℕ) ≠ 0) hab)
    simpa [Function.comp_def] using h
  have h1 :
      Summable (fun k => Real.log (q (3 * k + 2))) := by
    have h := hq.comp_injective
      (show Function.Injective (fun k : ℕ => 3 * k + 1) by
        intro a b hab
        have hmul : 3 * a = 3 * b := Nat.add_right_cancel hab
        exact mul_left_cancel₀ (by norm_num : (3 : ℕ) ≠ 0) hmul)
    simpa [Function.comp_def] using h
  have h2 :
      Summable (fun k => Real.log (q (3 * k + 3))) := by
    have h := hq.comp_injective
      (show Function.Injective (fun k : ℕ => 3 * k + 2) by
        intro a b hab
        have hmul : 3 * a = 3 * b := Nat.add_right_cancel hab
        exact mul_left_cancel₀ (by norm_num : (3 : ℕ) ≠ 0) hmul)
    simpa [Function.comp_def, Nat.add_assoc] using h
  have hu :
      Summable (fun k => u (k + 1)) := by
    have hsum := (h0.add h1).add h2
    apply hsum.congr
    intro k
    rw [q_three_one, q_three_two, q_three_three,
      u_eq_log_sum (k + 1) (by omega)]
  exact u_not_summable_from_one hu

/--
Exercise 3096, gap 1; define the missing sequence `q`,
replace the ellipsis, and compare finite grouped partial sums.
-/
theorem gap1 :
    ∀ m, qLogPartialSum m = groupedPartialSum m := by
  exact grouped_sum_identity

/--
Exercise 3096, gap 2; replace the scalar big-O token by a
function-level logarithmic remainder.
-/
theorem gap2 :
    ((fun n => u n - Real.log (1 + mainAlpha n)) =O[atTop]
      comparisonTerm) := by
  exact logarithmic_remainder_isBigO

/-- Exercise 3096, gap 3; use the exact deviation sequence. -/
theorem gap3 :
    Tendsto alpha atTop (𝓝 0) := by
  exact alpha_tendsto_zero

/-- Exercise 3096, gap 4; the grouped formula starts at one. -/
theorem gap4 :
    ∀ n : ℕ, 1 ≤ n → alpha n < 0 := by
  exact alpha_neg

/-- Exercise 3096, gap 5. -/
theorem gap5 :
    ¬SummableFromOne alpha := by
  exact alpha_not_summable_from_one

/-- Exercise 3096, gap 6. -/
theorem gap6 :
    ¬SummableFromOne u := by
  exact u_not_summable_from_one

/-- Exercise 3096, gap 7; retain the now-explicit definition of `q`. -/
theorem gap7 :
    ¬SummableFromOne (fun n => Real.log (q n)) := by
  exact q_log_not_summable_from_one

end

end ProofGap.Exercise3096
