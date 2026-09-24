import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2739_3

noncomputable section

open Filter
open scoped BigOperators Topology

def fallingFactorial (y : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (y - k)

def risingShift (t : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, ((k + 1 : ℕ) + t)

def term (x y : ℝ) (n : ℕ) : ℝ :=
  (Real.exp 1 * x) ^ n * fallingFactorial y n / (n : ℝ) ^ n

def isNonnegativeInteger (y : ℝ) : Prop :=
  ∃ m : ℕ, y = m

def ratioAbs (x y : ℝ) (n : ℕ) : ℝ :=
  |term x y n / term x y (n + 1)|

def boundaryRemainder (y : ℝ) (n : ℕ) : ℝ :=
  ratioAbs 1 y (n + 1) -
    (1 + (y + 1 / 2) / ((n + 1 : ℕ) : ℝ))

def rationalFactor (y : ℝ) (n : ℕ) : ℝ :=
  ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) - y)

def exponentialFactor (n : ℕ) : ℝ :=
  (1 / Real.exp 1) *
    (1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)

def rationalFactorRemainder (y : ℝ) (n : ℕ) : ℝ :=
  rationalFactor y n -
    (1 + (1 + y) / ((n + 1 : ℕ) : ℝ))

def exponentialFactorRemainder (n : ℕ) : ℝ :=
  exponentialFactor n -
    (1 - 1 / (2 * ((n + 1 : ℕ) : ℝ)))

def productRemainder (y : ℝ) (n : ℕ) : ℝ :=
  rationalFactor y n * exponentialFactor n -
    (1 + (y + 1 / 2) / ((n + 1 : ℕ) : ℝ))

def minusBoundaryRemainder (y : ℝ) (n : ℕ) : ℝ :=
  term (-1) y (n + 1) / term (-1) y (n + 2) -
    (1 + (y + 1 / 2) / ((n + 1 : ℕ) : ℝ))

def boundaryComparison (y : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (-(y + 1 / 2))

def ConditionallySummable (x y : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term x y (n + 1)) ∧
    ¬ Summable (fun n : ℕ => |term x y (n + 1)|)

private theorem fallingFactorial_ne_zero {y : ℝ}
    (hy : ¬ isNonnegativeInteger y) (n : ℕ) :
    fallingFactorial y n ≠ 0 := by
  unfold fallingFactorial
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk hzero
  apply hy
  refine ⟨k, ?_⟩
  have : y = (k : ℝ) := by linarith
  exact this

private theorem term_ne_zero {x y : ℝ} (hx : x ≠ 0)
    (hy : ¬ isNonnegativeInteger y) (n : ℕ) (hn : n ≠ 0) :
    term x y n ≠ 0 := by
  unfold term
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (Real.exp_ne_zero 1) hx))
      (fallingFactorial_ne_zero hy n))
    (pow_ne_zero _ (by exact_mod_cast hn))

theorem gap1 (y : ℝ) (n : ℕ) :
    fallingFactorial y n =
      (-1 : ℝ) ^ n * risingShift (-(1 + y)) n := by
  induction n with
  | zero => simp [fallingFactorial, risingShift]
  | succ n ih =>
      simp only [fallingFactorial, risingShift, Finset.prod_range_succ] at ih ⊢
      rw [ih, pow_succ]
      push_cast
      ring

theorem gap2 (x y : ℝ) (m n : ℕ) (hy : y = m) (hmn : m < n) :
    term x y n = 0 := by
  subst y
  unfold term fallingFactorial
  have hm : m ∈ Finset.range n := Finset.mem_range.mpr hmn
  rw [Finset.prod_eq_zero hm]
  · simp
  · simp

theorem gap3 (x y : ℝ) (hy : isNonnegativeInteger y) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  rcases hy with ⟨m, hm⟩
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Iic m).subset ?_
  intro n hn
  simp only [Function.support, Set.mem_setOf_eq] at hn
  change n ≤ m
  by_contra hnm
  have hlt : m < n + 1 := by omega
  have hz := gap2 x y m (n + 1) hm hlt
  simp [hz] at hn

theorem gap4 (x y : ℝ) (n : ℕ) (hx : x ≠ 0)
    (hy : ¬ isNonnegativeInteger y) (hn : 1 ≤ n) :
    term x y n / term x y (n + 1) =
      -((n + 1 : ℕ) : ℝ) / (n - y) * (1 / (Real.exp 1 * x)) *
        (1 + 1 / (n : ℝ)) ^ n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hny : (n : ℝ) - y ≠ 0 := by
    intro h
    apply hy
    refine ⟨n, ?_⟩
    linarith
  have hex : Real.exp 1 * x ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero 1) hx
  have hfall := fallingFactorial_ne_zero hy n
  unfold fallingFactorial at hfall
  unfold term fallingFactorial
  rw [Finset.prod_range_succ]
  push_cast
  have hyn : y - (n : ℝ) ≠ 0 := by
    intro h
    apply hny
    linarith
  have hdenFall :
      y * (∏ k ∈ Finset.range n, (y - (k : ℝ))) -
          (∏ k ∈ Finset.range n, (y - (k : ℝ))) * (n : ℝ) ≠ 0 := by
    rw [show y * (∏ k ∈ Finset.range n, (y - (k : ℝ))) -
        (∏ k ∈ Finset.range n, (y - (k : ℝ))) * (n : ℝ) =
      (∏ k ∈ Finset.range n, (y - (k : ℝ))) * (y - n) by ring]
    exact mul_ne_zero hfall hyn
  have hbase : 1 + 1 / (n : ℝ) = (n + 1) / n := by
    field_simp [hn0]
  rw [hbase, div_pow, pow_succ]
  field_simp [hn0, hny, hyn, hdenFall, hex, hfall, pow_ne_zero _ hn0,
    pow_ne_zero _ hex]
  ring

theorem gap5 (x y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    -((n + 1 : ℕ) : ℝ) / (n + 1 - (1 + y)) *
          (1 / (Real.exp 1 * x)) * (1 + 1 / (n : ℝ)) ^ n =
      -((n + 1 : ℕ) : ℝ) / (n - y) *
          (1 / (Real.exp 1 * x)) * (1 + 1 / (n : ℝ)) ^ n := by
  push_cast
  ring

theorem gap6 (x y : ℝ) (n : ℕ) (hx : x ≠ 0)
    (hy : ¬ isNonnegativeInteger y) (hn : 1 ≤ n) :
    term x y n / term x y (n + 1) =
      -((n + 1 : ℕ) : ℝ) / (n - y) * (1 / (Real.exp 1 * x)) *
        (1 + 1 / (n : ℝ)) ^ n := by
  exact gap4 x y n hx hy hn

private theorem inv_succ_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  simpa [Function.comp_def] using hbase.comp (tendsto_add_atTop_nat 1)

private theorem rationalFactor_tendsto (y : ℝ) :
    Tendsto (rationalFactor y) atTop (𝓝 1) := by
  have hnum : Tendsto
      (fun n : ℕ => 1 + 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add inv_succ_tendsto_zero
  have hden : Tendsto
      (fun n : ℕ => 1 - y / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := y)).mul inv_succ_tendsto_zero)
  have hlim : Tendsto
      (fun n : ℕ =>
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) /
          (1 - y / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa using hnum.div hden one_ne_zero
  refine hlim.congr' (eventually_atTop.2 ?_)
  obtain ⟨N, hN⟩ := exists_nat_gt |y|
  refine ⟨N, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hyn : y < ((n + 1 : ℕ) : ℝ) := by
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hyN : y < (N : ℝ) := lt_of_le_of_lt (le_abs_self y) (by exact_mod_cast hN)
    push_cast
    linarith
  unfold rationalFactor
  push_cast
  field_simp [hnpos.ne', (sub_pos.mpr hyn).ne']
  ring

private theorem exponentialFactor_tendsto :
    Tendsto exponentialFactor atTop (𝓝 1) := by
  have hpow := (Real.tendsto_one_add_div_pow_exp (1 : ℝ)).comp
    (tendsto_add_atTop_nat 1)
  have hmul := (tendsto_const_nhds (x := 1 / Real.exp 1)).mul hpow
  convert hmul using 1 <;>
    simp [exponentialFactor, Function.comp_def, div_eq_mul_inv,
      Real.exp_ne_zero, Nat.cast_add]

private theorem ratioAbs_eventually_eq (x y : ℝ) (hx : x ≠ 0)
    (hy : ¬ isNonnegativeInteger y) :
    (fun n : ℕ => ratioAbs x y (n + 1)) =ᶠ[atTop]
      fun n : ℕ => rationalFactor y n * exponentialFactor n / |x| := by
  obtain ⟨N, hN⟩ := exists_nat_gt |y|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hyn : y < ((n + 1 : ℕ) : ℝ) := by
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hyN : y < (N : ℝ) := lt_of_le_of_lt (le_abs_self y) (by exact_mod_cast hN)
    push_cast
    linarith
  have hden : 0 < ((n + 1 : ℕ) : ℝ) - y := sub_pos.mpr hyn
  have hxabs : 0 < |x| := abs_pos.mpr hx
  unfold ratioAbs
  rw [gap4 x y (n + 1) hx hy (by omega)]
  unfold rationalFactor exponentialFactor
  push_cast
  push_cast at hden
  simp only [abs_mul, abs_div, abs_neg, abs_inv, abs_pow, abs_one]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1 + 1),
    abs_of_pos hden, abs_of_pos (Real.exp_pos 1),
    abs_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1))]
  field_simp [hxabs.ne', (Real.exp_ne_zero 1), hden.ne']
  ring

theorem gap7 (x y : ℝ) (hx : x ≠ 0) (hy : ¬ isNonnegativeInteger y) :
    Tendsto (fun n : ℕ => ratioAbs x y (n + 1))
      atTop (nhds (1 / |x|)) := by
  have hprod : Tendsto
      (fun n : ℕ => rationalFactor y n * exponentialFactor n)
      atTop (𝓝 1) := by
    simpa using (rationalFactor_tendsto y).mul exponentialFactor_tendsto
  have hlim : Tendsto
      (fun n : ℕ => rationalFactor y n * exponentialFactor n / |x|)
      atTop (𝓝 (1 / |x|)) := by
    simpa using hprod.div_const |x|
  exact hlim.congr' (ratioAbs_eventually_eq x y hx hy).symm

theorem gap8 (x : ℝ) (hx0 : x ≠ 0) (hx : |x| < 1) :
    1 < 1 / |x| := by
  exact (one_lt_div (abs_pos.mpr hx0)).2 hx

theorem gap9 (x y : ℝ) (hx0 : x ≠ 0) (hx : |x| < 1)
    (hy : ¬ isNonnegativeInteger y) :
    ∀ᶠ n : ℕ in atTop, 1 < ratioAbs x y (n + 1) := by
  exact (tendsto_order.1 (gap7 x y hx0 hy)).1 1 (gap8 x hx0 hx)

private theorem forwardRatio_tendsto (x y : ℝ) (hx : x ≠ 0)
    (hy : ¬ isNonnegativeInteger y) :
    Tendsto
      (fun n : ℕ =>
        |term x y (n + 2)| / |term x y (n + 1)|)
      atTop (𝓝 |x|) := by
  have h := gap7 x y hx hy
  have hlim0 : 1 / |x| ≠ 0 := one_div_ne_zero (abs_ne_zero.mpr hx)
  have hi := h.inv₀ hlim0
  convert hi using 1
  · funext n
    unfold ratioAbs
    rw [abs_div]
    have h1 : |term x y (n + 1)| ≠ 0 :=
      abs_ne_zero.mpr (term_ne_zero hx hy (n + 1) (Nat.succ_ne_zero n))
    have h2 : |term x y (n + 2)| ≠ 0 :=
      abs_ne_zero.mpr (term_ne_zero hx hy (n + 2) (by omega))
    field_simp [h1, h2]
  · field_simp [abs_ne_zero.mpr hx]

theorem gap10 (x y : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  by_cases hx0 : x = 0
  · subst x
    simp [term]
  by_cases hy : isNonnegativeInteger y
  · exact gap3 x y hy
  have hne : ∀ᶠ n : ℕ in atTop, term x y (n + 1) ≠ 0 :=
    Eventually.of_forall (fun n =>
      term_ne_zero hx0 hy (n + 1) (Nat.succ_ne_zero n))
  have hs : Summable (fun n : ℕ => term x y (n + 1)) :=
    summable_of_ratio_test_tendsto_lt_one hx hne
      (by simpa [Real.norm_eq_abs] using forwardRatio_tendsto x y hx0 hy)
  exact hs.abs

theorem gap11 (x y : ℝ) (hx : 1 < |x|) (hy : ¬ isNonnegativeInteger y) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |term x y n| < |term x y (n + 1)| := by
  have hx0 : x ≠ 0 := abs_ne_zero.mp (ne_of_gt (zero_lt_one.trans hx))
  have hevent : ∀ᶠ n : ℕ in atTop,
      1 < |term x y (n + 2)| / |term x y (n + 1)| :=
    (tendsto_order.1 (forwardRatio_tendsto x y hx0 hy)).1 1 hx
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hprev : 0 < |term x y n| :=
    abs_pos.mpr (term_ne_zero hx0 hy n (Nat.ne_of_gt hn1))
  have hr := hN (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega] at hr
  simpa using (lt_div_iff₀ hprev).mp hr

theorem gap12 (x y : ℝ) (hx : 1 < |x|) (hy : ¬ isNonnegativeInteger y) :
    ¬ Summable (fun n : ℕ => term x y (n + 1)) := by
  have hx0 : x ≠ 0 := abs_ne_zero.mp (ne_of_gt (zero_lt_one.trans hx))
  exact not_summable_of_ratio_test_tendsto_gt_one hx
    (by simpa [Real.norm_eq_abs] using forwardRatio_tendsto x y hx0 hy)

theorem gap13 (x y : ℝ) (hx : |x| = 1)
    (hy : ¬ isNonnegativeInteger y) :
    ∀ n : ℕ, 1 ≤ n → y < n →
      ratioAbs x y n =
        ((n + 1 : ℕ) : ℝ) / (n - y) * (1 / Real.exp 1) *
          (1 + 1 / (n : ℝ)) ^ n := by
  intro n hn hyn
  have hx0 : x ≠ 0 := abs_ne_zero.mp (by rw [hx]; exact one_ne_zero)
  have hden : 0 < (n : ℝ) - y := sub_pos.mpr hyn
  have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
  unfold ratioAbs
  rw [gap4 x y n hx0 hy hn]
  push_cast
  simp only [abs_mul, abs_div, abs_neg, abs_inv, abs_pow, abs_one]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1),
    abs_of_pos hden, abs_of_pos (Real.exp_pos 1), hx, mul_one,
    abs_of_pos hbase]

private theorem rationalFactorRemainder_bound (y : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      |rationalFactorRemainder y n| ≤
        (2 * |y * (1 + y)|) /
          (((n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * |y| + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  let r : ℝ := ((n + 1 : ℕ) : ℝ)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hNr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hry : 2 * |y| < r := by
    have hN' : 2 * |y| + 1 < (N : ℝ) := by exact_mod_cast hN
    dsimp [r]
    push_cast
    linarith
  have hrypos : 0 < r - y := by
    have := le_abs_self y
    linarith
  have hhalf : r / 2 ≤ r - y := by
    have := le_abs_self y
    linarith
  have heq : rationalFactorRemainder y n =
      y * (1 + y) / (r * (r - y)) := by
    dsimp [r]
    unfold rationalFactorRemainder rationalFactor
    push_cast
    have hd : (n : ℝ) + 1 - y ≠ 0 := by
      dsimp [r] at hrypos
      push_cast at hrypos
      exact (ne_of_gt hrypos)
    field_simp [hd]
    ring
  rw [heq]
  simp only [abs_div, abs_mul, abs_of_pos hrpos, abs_of_pos hrypos]
  have hden : r ^ 2 / 2 ≤ r * (r - y) := by
    nlinarith
  have hnum : 0 ≤ |y * (1 + y)| := abs_nonneg _
  change |y| * |1 + y| / (r * (r - y)) ≤
    (2 * (|y| * |1 + y|)) / r ^ 2
  apply (div_le_div_iff₀ (mul_pos hrpos hrypos) (sq_pos_of_pos hrpos)).2
  have hden' : r ^ 2 ≤ 2 * (r * (r - y)) := by nlinarith
  have hnum' : 0 ≤ |y| * |1 + y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hden' hnum']

private theorem log_second_order_bound (N : ℕ) (hN : 2 ≤ N) :
    |Real.log (1 + 1 / (N : ℝ)) -
        (1 / (N : ℝ) - 1 / (2 * (N : ℝ) ^ 2))| ≤
      1 / (N : ℝ) ^ 3 := by
  let t : ℝ := 1 / (N : ℝ)
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have ht : 0 < t := one_div_pos.mpr hNr
  have ht12 : t ≤ 1 / 2 := by
    dsimp [t]
    rw [div_le_iff₀ hNr]
    have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hzt : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    linarith
  have hc := Complex.norm_log_sub_logTaylor_le 2 hzt
  have hlogcast : Complex.log (1 + (t : ℂ)) =
      (Real.log (1 + t) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]
    exact (Complex.ofReal_log (by linarith)).symm
  have htaylor : Complex.logTaylor 3 (t : ℂ) =
      ((t - t ^ 2 / 2 : ℝ) : ℂ) := by
    simp [Complex.logTaylor_succ, Complex.logTaylor_zero]
    ring
  rw [hlogcast, htaylor, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hc
  have hinv : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    norm_num
    linarith
  have hraw : |Real.log (1 + t) - (t - t ^ 2 / 2)| ≤ t ^ 3 := by
    calc
      |Real.log (1 + t) - (t - t ^ 2 / 2)| ≤
          t ^ 3 * (1 - t)⁻¹ / 3 := by
            norm_num at hc
            simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using hc
      _ ≤ t ^ 3 := by
        have ht30 : 0 ≤ t ^ 3 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hinv ht30]
  dsimp [t] at hraw ⊢
  convert hraw using 1 <;> field_simp [hNr.ne'] <;> ring

private theorem scaled_log_error_bound (N : ℕ) (hN : 2 ≤ N) :
    |(N : ℝ) * Real.log (1 + 1 / (N : ℝ)) -
        (1 - 1 / (2 * (N : ℝ)))| ≤
      1 / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have h := log_second_order_bound N hN
  have hm := mul_le_mul_of_nonneg_left h hNr.le
  calc
    |(N : ℝ) * Real.log (1 + 1 / (N : ℝ)) -
        (1 - 1 / (2 * (N : ℝ)))| =
        |(N : ℝ) * (Real.log (1 + 1 / (N : ℝ)) -
          (1 / (N : ℝ) - 1 / (2 * (N : ℝ) ^ 2)))| := by
            congr 1
            field_simp [hNr.ne']
    _ = (N : ℝ) * |Real.log (1 + 1 / (N : ℝ)) -
          (1 / (N : ℝ) - 1 / (2 * (N : ℝ) ^ 2))| := by
            rw [abs_mul, abs_of_pos hNr]
    _ ≤ (N : ℝ) * (1 / (N : ℝ) ^ 3) := hm
    _ = 1 / (N : ℝ) ^ 2 := by
      field_simp [hNr.ne']

private theorem exponentialFactor_eq_exp (n : ℕ) :
    exponentialFactor n =
      Real.exp (((n + 1 : ℕ) : ℝ) *
        Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) - 1) := by
  let N : ℕ := n + 1
  have hbase : 0 < 1 + 1 / (N : ℝ) := by positivity
  unfold exponentialFactor
  change (1 / Real.exp 1) * (1 + 1 / (N : ℝ)) ^ N = _
  calc
    (1 / Real.exp 1) * (1 + 1 / (N : ℝ)) ^ N =
        Real.exp (-1) * (Real.exp (Real.log (1 + 1 / (N : ℝ)))) ^ N := by
          rw [Real.exp_log hbase]
          simp only [one_div, Real.exp_neg]
    _ = Real.exp (-1 + (N : ℝ) * Real.log (1 + 1 / (N : ℝ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ = Real.exp (((n + 1 : ℕ) : ℝ) *
        Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) - 1) := by
      congr 1
      dsimp [N]
      push_cast
      ring

private theorem exponentialFactorRemainder_bound :
    ∀ n : ℕ, 1 ≤ n →
      |exponentialFactorRemainder n| ≤
        2 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  intro n hn
  let N : ℕ := n + 1
  let A : ℝ := (N : ℝ) * Real.log (1 + 1 / (N : ℝ)) - 1
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hNr : (0 : ℝ) < (N : ℝ) := by positivity
  have herr0 := scaled_log_error_bound N hN
  have herr : |A + 1 / (2 * (N : ℝ))| ≤ 1 / (N : ℝ) ^ 2 := by
    dsimp [A]
    convert herr0 using 1 <;> ring
  have hA : |A| ≤ 1 / (N : ℝ) := by
    calc
      |A| = |(A + 1 / (2 * (N : ℝ))) - 1 / (2 * (N : ℝ))| := by ring_nf
      _ ≤ |A + 1 / (2 * (N : ℝ))| + |1 / (2 * (N : ℝ))| := abs_sub _ _
      _ ≤ 1 / (N : ℝ) ^ 2 + 1 / (2 * (N : ℝ)) := by
        apply add_le_add herr
        rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (N : ℝ)))]
      _ ≤ 1 / (N : ℝ) := by
        have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        field_simp [hNr.ne']
        nlinarith
  have hA1 : ‖A‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact hA.trans (by
      rw [div_le_one hNr]
      exact_mod_cast (one_le_two.trans hN))
  have hexp := Real.norm_exp_sub_one_sub_id_le hA1
  have hexp' : |Real.exp A - 1 - A| ≤ A ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hexp
  unfold exponentialFactorRemainder
  rw [exponentialFactor_eq_exp]
  change |Real.exp A - (1 - 1 / (2 * (N : ℝ)))| ≤ _
  calc
    |Real.exp A - (1 - 1 / (2 * (N : ℝ)))| =
        |(Real.exp A - 1 - A) + (A + 1 / (2 * (N : ℝ)))| := by ring_nf
    _ ≤ |Real.exp A - 1 - A| + |A + 1 / (2 * (N : ℝ))| := abs_add_le _ _
    _ ≤ A ^ 2 + 1 / (N : ℝ) ^ 2 := add_le_add hexp' herr
    _ ≤ 2 / (N : ℝ) ^ 2 := by
      have hAsq : A ^ 2 ≤ (1 / (N : ℝ)) ^ 2 :=
        by simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg A) (by positivity)).2 hA
      have hone : (1 / (N : ℝ)) ^ 2 = 1 / (N : ℝ) ^ 2 := by
        field_simp [hNr.ne']
      rw [hone] at hAsq
      calc
        A ^ 2 + 1 / (N : ℝ) ^ 2 ≤
            1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) ^ 2 :=
          add_le_add_left hAsq _
        _ = 2 / (N : ℝ) ^ 2 := by ring

theorem gap14 (y : ℝ) (hy : ¬ isNonnegativeInteger y) :
    Asymptotics.IsBigO atTop (rationalFactorRemainder y)
        (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) ∧
      Asymptotics.IsBigO atTop exponentialFactorRemainder
        (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) ∧
      (∀ᶠ n : ℕ in atTop,
        ratioAbs 1 y (n + 1) = rationalFactor y n * exponentialFactor n) := by
  refine ⟨?_, ?_, ?_⟩
  · refine Asymptotics.IsBigO.of_bound (2 * |y * (1 + y)|) ?_
    filter_upwards [rationalFactorRemainder_bound y] with n hn
    simpa [Real.norm_eq_abs, abs_of_pos (by positivity :
      (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) ^ 2)), div_eq_mul_inv] using hn
  · refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := exponentialFactorRemainder_bound n hn
    simpa [Real.norm_eq_abs, abs_of_pos (by positivity :
      (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) ^ 2)), div_eq_mul_inv] using h
  · filter_upwards [ratioAbs_eventually_eq 1 y one_ne_zero hy] with n hn
    simpa using hn

theorem gap15 (y : ℝ) :
    Asymptotics.IsBigO atTop (productRemainder y)
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  let g : ℕ → ℝ := fun n => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)
  have hr : Asymptotics.IsBigO atTop (rationalFactorRemainder y) g := by
    refine Asymptotics.IsBigO.of_bound (2 * |y * (1 + y)|) ?_
    filter_upwards [rationalFactorRemainder_bound y] with n hn
    simpa [g, Real.norm_eq_abs, abs_of_pos (by positivity :
      (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) ^ 2)), div_eq_mul_inv] using hn
  have he : Asymptotics.IsBigO atTop exponentialFactorRemainder g := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := exponentialFactorRemainder_bound n hn
    simpa [g, Real.norm_eq_abs, abs_of_pos (by positivity :
      (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) ^ 2)), div_eq_mul_inv] using h
  have hEF : Asymptotics.IsBigO atTop exponentialFactor (fun _ : ℕ => (1 : ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto exponentialFactor_tendsto one_ne_zero
  have hbaseT : Tendsto
      (fun n : ℕ => 1 + (1 + y) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (1 + y : ℝ))).mul inv_succ_tendsto_zero)
  have hbase : Asymptotics.IsBigO atTop
      (fun n : ℕ => 1 + (1 + y) / ((n + 1 : ℕ) : ℝ))
      (fun _ : ℕ => (1 : ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto hbaseT one_ne_zero
  have hrEF : Asymptotics.IsBigO atTop
      (fun n => rationalFactorRemainder y n * exponentialFactor n) g := by
    simpa [g] using hr.mul hEF
  have hbaseE : Asymptotics.IsBigO atTop
      (fun n => (1 + (1 + y) / ((n + 1 : ℕ) : ℝ)) *
        exponentialFactorRemainder n) g := by
    simpa [g] using hbase.mul he
  have hdet : Asymptotics.IsBigO atTop
      (fun n : ℕ => -(1 + y) / (2 * (((n + 1 : ℕ) : ℝ) ^ 2))) g := by
    have h := (Asymptotics.isBigO_refl g atTop).const_mul_left (-(1 + y) / 2)
    convert h using 1
    funext n
    dsimp [g]
    ring
  have hsum := (hrEF.add hbaseE).add hdet
  convert hsum using 1
  · funext n
    unfold productRemainder rationalFactorRemainder exponentialFactorRemainder
    ring

theorem gap16 (y : ℝ) (hy : ¬ isNonnegativeInteger y) :
    Asymptotics.IsBigO atTop (boundaryRemainder y)
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  apply (gap15 y).congr'
  · filter_upwards [ratioAbs_eventually_eq 1 y one_ne_zero hy] with n hn
    unfold boundaryRemainder productRemainder
    simpa using congrArg
      (fun z : ℝ => z - (1 + (y + 1 / 2) / ((n + 1 : ℕ) : ℝ))) hn.symm
  · exact Filter.EventuallyEq.rfl

private theorem gammaSeq_mul_fallingFactorial (y : ℝ)
    (hy : ¬ isNonnegativeInteger y) (n : ℕ) :
    |Real.GammaSeq (-y) n| * |fallingFactorial y (n + 1)| =
      (n : ℝ) ^ (-y) * (n.factorial : ℝ) := by
  have hprod :
      (∏ j ∈ Finset.range (n + 1), ((-y) + (j : ℝ))) =
        risingShift (-(1 + y)) (n + 1) := by
    unfold risingShift
    apply Finset.prod_congr rfl
    intro j hj
    push_cast
    ring
  have hfall : fallingFactorial y (n + 1) ≠ 0 :=
    fallingFactorial_ne_zero hy (n + 1)
  have hrise : risingShift (-(1 + y)) (n + 1) ≠ 0 := by
    intro h
    apply hfall
    rw [gap1 y (n + 1), h]
    simp
  have hnum : 0 ≤ (n : ℝ) ^ (-y) * (n.factorial : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _) (by positivity)
  unfold Real.GammaSeq
  rw [hprod, abs_div, abs_of_nonneg hnum, gap1]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  field_simp [abs_ne_zero.mpr hrise]

private theorem term_mul_gammaSeq (y : ℝ)
    (hy : ¬ isNonnegativeInteger y) (n : ℕ) :
    |term 1 y (n + 1)| * |Real.GammaSeq (-y) n| =
      (Real.exp 1) ^ (n + 1) *
        ((n : ℝ) ^ (-y) * (n.factorial : ℝ)) /
          (((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold term
  simp only [mul_one, abs_div, abs_mul, abs_pow]
  rw [abs_of_pos (Real.exp_pos 1), abs_of_pos hNpos]
  calc
    Real.exp 1 ^ (n + 1) * |fallingFactorial y (n + 1)| /
          ((n + 1 : ℕ) : ℝ) ^ (n + 1) * |Real.GammaSeq (-y) n| =
        Real.exp 1 ^ (n + 1) *
          (|Real.GammaSeq (-y) n| * |fallingFactorial y (n + 1)|) /
            ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by ring
    _ = Real.exp 1 ^ (n + 1) *
        ((n : ℝ) ^ (-y) * (n.factorial : ℝ)) /
          ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
      rw [gammaSeq_mul_fallingFactorial y hy n]

private theorem exp_power_factor_tendsto :
    Tendsto
      (fun n : ℕ =>
        Real.exp 1 ^ (n + 1) * ((n : ℝ) / Real.exp 1) ^ n /
          (((n + 1 : ℕ) : ℝ) ^ n))
      atTop (𝓝 1) := by
  have hinv := (Real.tendsto_one_add_div_pow_exp (1 : ℝ)).inv₀
    (Real.exp_ne_zero 1)
  have hmul := (tendsto_const_nhds (x := Real.exp 1)).mul hinv
  have hmul' : Tendsto
      (fun n : ℕ => Real.exp 1 * ((1 + 1 / (n : ℝ)) ^ n)⁻¹)
      atTop (𝓝 1) := by
    convert hmul using 1
    field_simp [Real.exp_ne_zero]
  have hratio : Tendsto
      (fun n : ℕ => Real.exp 1 * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ n)
      atTop (𝓝 1) := by
    apply hmul'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    congr 1
    rw [← inv_pow]
    congr 1
    push_cast
    field_simp [hn0]
  apply hratio.congr'
  filter_upwards with n
  rw [pow_succ, div_pow, div_pow]
  field_simp [Real.exp_ne_zero]
  <;> ring

private theorem polynomial_factor_tendsto (y : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) ^ (-y) * Real.sqrt (2 * n) *
          (((n + 1 : ℕ) : ℝ) ^ (y + 1 / 2)) /
            ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (Real.sqrt 2)) := by
  have hratioUp : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      tendsto_one_div_atTop_nhds_zero_nat
    have h' : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    push_cast
    field_simp [hn0]
  have hpow : Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ y))
      atTop (𝓝 1) := by
    simpa using hratioUp.rpow_const (Or.inl one_ne_zero)
  have hratioDown : Tendsto
      (fun n : ℕ => (2 : ℝ) * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt ((2 : ℝ) * ((n : ℝ) / ((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (Real.sqrt 2)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hratioDown
  have hprod := hpow.mul hsqrt
  have hlim : (1 : ℝ) * Real.sqrt 2 = Real.sqrt 2 := one_mul _
  rw [hlim] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsqrtN : Real.sqrt (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [Real.rpow_add hNpos, ← Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hnpos.le, Real.div_rpow hNpos.le hnpos.le]
  rw [show Real.sqrt ((2 : ℝ) * ((n : ℝ) / ((n + 1 : ℕ) : ℝ))) =
      Real.sqrt (2 * n) / Real.sqrt (((n + 1 : ℕ) : ℝ)) by
    rw [show (2 : ℝ) * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) =
        (2 * n) / ((n + 1 : ℕ) : ℝ) by ring,
      Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * n),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]]
  have hsq := Real.sq_sqrt hNpos.le
  field_simp [Real.rpow_pos_of_pos hnpos y |>.ne', hsqrtN]
  nlinarith

private theorem scaled_normalized_term_eq (y : ℝ)
    (hy : ¬ isNonnegativeInteger y) (n : ℕ) (hn : 1 ≤ n) :
    (|term 1 y (n + 1)| / boundaryComparison y (n + 1)) *
        |Real.GammaSeq (-y) n| =
      Stirling.stirlingSeq n *
        (Real.exp 1 ^ (n + 1) * ((n : ℝ) / Real.exp 1) ^ n /
          (((n + 1 : ℕ) : ℝ) ^ n)) *
        ((n : ℝ) ^ (-y) * Real.sqrt (2 * n) *
          (((n + 1 : ℕ) : ℝ) ^ (y + 1 / 2)) /
            ((n + 1 : ℕ) : ℝ)) := by
  have ht := term_mul_gammaSeq y hy n
  calc
    (|term 1 y (n + 1)| / boundaryComparison y (n + 1)) *
          |Real.GammaSeq (-y) n| =
        (|term 1 y (n + 1)| * |Real.GammaSeq (-y) n|) /
          boundaryComparison y (n + 1) := by ring
    _ = (Real.exp 1) ^ (n + 1) *
          ((n : ℝ) ^ (-y) * (n.factorial : ℝ)) /
            (((n + 1 : ℕ) : ℝ) ^ (n + 1)) /
          boundaryComparison y (n + 1) := by rw [ht]
    _ = Stirling.stirlingSeq n *
        (Real.exp 1 ^ (n + 1) * ((n : ℝ) / Real.exp 1) ^ n /
          (((n + 1 : ℕ) : ℝ) ^ n)) *
        ((n : ℝ) ^ (-y) * Real.sqrt (2 * n) *
          (((n + 1 : ℕ) : ℝ) ^ (y + 1 / 2)) /
            ((n + 1 : ℕ) : ℝ)) := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hsqrt : Real.sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
      have hpow : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
      have hb : boundaryComparison y (n + 1) =
          ((((n + 1 : ℕ) : ℝ) ^ (y + 1 / 2)))⁻¹ := by
        unfold boundaryComparison
        exact Real.rpow_neg hNpos.le _
      rw [hb, div_inv_eq_mul, pow_succ]
      unfold Stirling.stirlingSeq
      field_simp [hsqrt, hpow, hNpos.ne', Real.exp_ne_zero]
      <;> ring

private theorem normalized_term_tendsto (y : ℝ)
    (hy : ¬ isNonnegativeInteger y) :
    Tendsto
      (fun n : ℕ => |term 1 y (n + 1)| / boundaryComparison y (n + 1))
      atTop (𝓝 (Real.sqrt 2 * Real.sqrt Real.pi / |Real.Gamma (-y)|)) := by
  have hG : Real.Gamma (-y) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro m hm
    apply hy
    refine ⟨m, ?_⟩
    exact neg_inj.mp (hm.trans (by push_cast; rfl))
  have hGamma : Tendsto (fun n : ℕ => |Real.GammaSeq (-y) n|)
      atTop (𝓝 |Real.Gamma (-y)|) :=
    (Real.GammaSeq_tendsto_Gamma (-y)).abs
  have hcore := (Stirling.tendsto_stirlingSeq_sqrt_pi.mul
      exp_power_factor_tendsto).mul (polynomial_factor_tendsto y)
  have hscaled : Tendsto
      (fun n : ℕ =>
        (|term 1 y (n + 1)| / boundaryComparison y (n + 1)) *
          |Real.GammaSeq (-y) n|)
      atTop (𝓝 (Real.sqrt 2 * Real.sqrt Real.pi)) := by
    have hc : Tendsto
        (fun n : ℕ => Stirling.stirlingSeq n *
          (Real.exp 1 ^ (n + 1) * ((n : ℝ) / Real.exp 1) ^ n /
            (((n + 1 : ℕ) : ℝ) ^ n)) *
          ((n : ℝ) ^ (-y) * Real.sqrt (2 * n) *
            (((n + 1 : ℕ) : ℝ) ^ (y + 1 / 2)) /
              ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 (Real.sqrt 2 * Real.sqrt Real.pi)) := by
      convert hcore using 1 <;> ring
    apply hc.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (scaled_normalized_term_eq y hy n hn).symm
  have hdiv := hscaled.div hGamma (abs_ne_zero.mpr hG)
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hGn : |Real.GammaSeq (-y) n| ≠ 0 := by
      rw [abs_ne_zero]
      unfold Real.GammaSeq
      have hprod : (∏ j ∈ Finset.range (n + 1), ((-y) + (j : ℝ))) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj hz
        apply hy
        refine ⟨j, ?_⟩
        linarith
      exact div_ne_zero
        (mul_ne_zero (Real.rpow_pos_of_pos hnpos _).ne' (by positivity)) hprod
    change ((|term 1 y (n + 1)| / boundaryComparison y (n + 1) *
      |Real.GammaSeq (-y) n|) / |Real.GammaSeq (-y) n|) = _
    field_simp [hGn]

private theorem normalized_limit_pos (y : ℝ)
    (hy : ¬ isNonnegativeInteger y) :
    0 < Real.sqrt 2 * Real.sqrt Real.pi / |Real.Gamma (-y)| := by
  have hG : Real.Gamma (-y) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro m hm
    apply hy
    refine ⟨m, ?_⟩
    linarith
  positivity

private theorem term_boundary_comparison (y : ℝ)
    (hy : ¬ isNonnegativeInteger y) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        c * boundaryComparison y (n + 1) ≤ |term 1 y (n + 1)| ∧
          |term 1 y (n + 1)| ≤ C * boundaryComparison y (n + 1) := by
  let L : ℝ := Real.sqrt 2 * Real.sqrt Real.pi / |Real.Gamma (-y)|
  have hL : 0 < L := normalized_limit_pos y hy
  have ht := normalized_term_tendsto y hy
  have hlo : ∀ᶠ n : ℕ in atTop,
      L / 2 < |term 1 y (n + 1)| / boundaryComparison y (n + 1) :=
    (tendsto_order.1 ht).1 (L / 2) (by linarith)
  have hhi : ∀ᶠ n : ℕ in atTop,
      |term 1 y (n + 1)| / boundaryComparison y (n + 1) < 2 * L :=
    (tendsto_order.1 ht).2 (2 * L) (by linarith)
  refine ⟨L / 2, 2 * L, by linarith, by linarith, ?_⟩
  filter_upwards [hlo, hhi] with n hnlo hnhi
  have hb : 0 < boundaryComparison y (n + 1) := by
    unfold boundaryComparison
    exact Real.rpow_pos_of_pos (by positivity) _
  exact ⟨(lt_div_iff₀ hb).mp hnlo |>.le, (div_lt_iff₀ hb).mp hnhi |>.le⟩

private theorem abs_term_eq_abs_term_one (x y : ℝ) (hx : |x| = 1) (n : ℕ) :
    |term x y n| = |term 1 y n| := by
  unfold term
  simp only [abs_div, abs_mul, abs_pow, abs_one, mul_one]
  rw [hx]
  simp

private theorem boundaryComparison_summable (y : ℝ) (hy : 1 / 2 < y) :
    Summable (fun n : ℕ => boundaryComparison y (n + 1)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(y + 1 / 2))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift := (summable_nat_add_iff 1).mpr hs
  simpa [boundaryComparison, Nat.add_comm] using hshift

private theorem boundaryComparison_not_summable (y : ℝ) (hy : y ≤ 1 / 2) :
    ¬ Summable (fun n : ℕ => boundaryComparison y (n + 1)) := by
  intro hs
  have hshift : Summable
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-(y + 1 / 2)))) := by
    simpa [boundaryComparison, Nat.add_comm] using hs
  have hall : Summable (fun n : ℕ => (n : ℝ) ^ (-(y + 1 / 2))) :=
    (summable_nat_add_iff 1).mp hshift
  have hp := Real.summable_nat_rpow.mp hall
  linarith

private theorem boundaryComparison_tendsto_zero (y : ℝ) (hy : -1 / 2 < y) :
    Tendsto (fun n : ℕ => boundaryComparison y (n + 1)) atTop (𝓝 0) := by
  have hp : 0 < y + 1 / 2 := by linarith
  have h := (tendsto_rpow_neg_atTop hp).comp
    ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  simpa [boundaryComparison, Function.comp_def] using h

theorem gap17 (x y : ℝ) (hx : |x| = 1) (hy : 1 / 2 < y) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  by_cases hy0 : isNonnegativeInteger y
  · exact gap3 x y hy0
  obtain ⟨c, C, hc, hC, hbounds⟩ := term_boundary_comparison y hy0
  have hs := boundaryComparison_summable y hy
  have hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => |term 1 y (n + 1)|)
      (fun n : ℕ => boundaryComparison y (n + 1)) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hbounds] with n hn
    have hbpos : 0 < boundaryComparison y (n + 1) := by
      unfold boundaryComparison
      exact Real.rpow_pos_of_pos (by positivity) _
    simpa [Real.norm_eq_abs, abs_of_pos hbpos] using hn.2
  have hs1 : Summable (fun n : ℕ => |term 1 y (n + 1)|) :=
    summable_of_isBigO_nat hs hO
  exact hs1.congr (fun n => (abs_term_eq_abs_term_one x y hx (n + 1)).symm)

theorem gap18 (x y : ℝ) (hx : |x| = 1) (hy0 : ¬ isNonnegativeInteger y)
    (hy : y ≤ 1 / 2) :
    ¬ Summable (fun n : ℕ => |term x y (n + 1)|) := by
  intro hsx
  have hs : Summable (fun n : ℕ => |term 1 y (n + 1)|) :=
    hsx.congr (fun n => abs_term_eq_abs_term_one x y hx (n + 1))
  obtain ⟨c, C, hc, hC, hbounds⟩ := term_boundary_comparison y hy0
  rcases eventually_atTop.1 hbounds with ⟨N, hN⟩
  have hshiftTerm : Summable (fun n : ℕ => |term 1 y (n + N + 1)|) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff N).mpr hs
  have hscaled : Summable
      (fun n : ℕ => (1 / c) * |term 1 y (n + N + 1)|) :=
    hshiftTerm.mul_left (1 / c)
  have hbshift : Summable
      (fun n : ℕ => boundaryComparison y (n + N + 1)) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => (1 / c) * |term 1 y (n + N + 1)|)
      (g := fun n : ℕ => boundaryComparison y (n + N + 1)) ?_ ?_ hscaled
    · intro n
      unfold boundaryComparison
      exact Real.rpow_nonneg (by positivity) _
    · intro n
      have hlow := (hN (n + N) (by omega)).1
      have hc0 : 0 < c := hc
      have hlow' : boundaryComparison y (n + N + 1) * c ≤
          |term 1 y (n + N + 1)| := by
        simpa [mul_comm] using hlow
      simpa [div_eq_mul_inv, one_div, mul_comm] using
        ((le_div_iff₀ hc0).2 hlow')
  have hb : Summable (fun n : ℕ => boundaryComparison y (n + 1)) := by
    apply (summable_nat_add_iff N).mp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbshift
  exact boundaryComparison_not_summable y hy hb

theorem gap19 (y : ℝ) (hy0 : ¬ isNonnegativeInteger y)
    (hy1 : -1 / 2 < y) (hy2 : y ≤ 1 / 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < term (-1) y n * term (-1) y (n + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |y|
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hNn : N ≤ n := le_trans (le_max_right 1 N) hn
  have hyn : y < (n : ℝ) := by
    have hyN : y < (N : ℝ) :=
      lt_of_le_of_lt (le_abs_self y) (by exact_mod_cast hN)
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
    linarith
  have hratio : 0 < term (-1) y n / term (-1) y (n + 1) := by
    rw [gap4 (-1) y n (by norm_num) hy0 hn1]
    have hden : 0 < (n : ℝ) - y := sub_pos.mpr hyn
    have hA : 0 < ((n + 1 : ℕ) : ℝ) / ((n : ℝ) - y) := by positivity
    have hE : 0 < 1 / Real.exp 1 := by positivity
    have hP : 0 < (1 + 1 / (n : ℝ)) ^ n := by positivity
    convert mul_pos (mul_pos hA hE) hP using 1
    field_simp [Real.exp_ne_zero]
    <;> ring
  have hnext : term (-1) y (n + 1) ≠ 0 :=
    term_ne_zero (by norm_num) hy0 (n + 1) (Nat.succ_ne_zero n)
  calc
    term (-1) y n * term (-1) y (n + 1) =
        (term (-1) y n / term (-1) y (n + 1)) *
          term (-1) y (n + 1) ^ 2 := by
            field_simp [hnext]
    _ > 0 := mul_pos hratio (sq_pos_of_ne_zero hnext)

theorem gap20 (y : ℝ) (hy : ¬ isNonnegativeInteger y) :
    Asymptotics.IsBigO atTop (minusBoundaryRemainder y)
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  apply (gap15 y).congr'
  · filter_upwards with n
    have hden : ((n + 1 : ℕ) : ℝ) - y ≠ 0 := by
      intro h
      apply hy
      refine ⟨n + 1, ?_⟩
      linarith
    unfold productRemainder minusBoundaryRemainder
    rw [gap4 (-1) y (n + 1) (by norm_num) hy (by omega)]
    unfold rationalFactor exponentialFactor
    push_cast
    field_simp [Real.exp_ne_zero, hden]
    <;> ring
  · exact Filter.EventuallyEq.rfl

theorem gap21 (y : ℝ) (hy0 : ¬ isNonnegativeInteger y)
    (hy1 : -1 / 2 < y) (hy2 : y ≤ 1 / 2) :
    ¬ Summable (fun n : ℕ => term (-1) y (n + 1)) := by
  intro hs
  exact gap18 (-1) y (by norm_num) hy0 hy2 hs.abs

theorem gap22 (y : ℝ) (hy : ¬ isNonnegativeInteger y) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      term 1 y n * term 1 y (n + 1) < 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |y|
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hNn : N ≤ n := le_trans (le_max_right 1 N) hn
  have hyn : y < (n : ℝ) := by
    have hyN : y < (N : ℝ) :=
      lt_of_le_of_lt (le_abs_self y) (by exact_mod_cast hN)
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
    linarith
  have hratio : term 1 y n / term 1 y (n + 1) < 0 := by
    rw [gap4 1 y n one_ne_zero hy hn1]
    have hden : 0 < (n : ℝ) - y := sub_pos.mpr hyn
    have hA : 0 < ((n + 1 : ℕ) : ℝ) / ((n : ℝ) - y) := by positivity
    have hE : 0 < 1 / Real.exp 1 := by positivity
    have hP : 0 < (1 + 1 / (n : ℝ)) ^ n := by positivity
    convert neg_neg_of_pos (mul_pos (mul_pos hA hE) hP) using 1
    field_simp [Real.exp_ne_zero]
    <;> ring
  have hnext : term 1 y (n + 1) ≠ 0 :=
    term_ne_zero one_ne_zero hy (n + 1) (Nat.succ_ne_zero n)
  calc
    term 1 y n * term 1 y (n + 1) =
        (term 1 y n / term 1 y (n + 1)) *
          term 1 y (n + 1) ^ 2 := by
            field_simp [hnext]
    _ < 0 := mul_neg_of_neg_of_pos hratio (sq_pos_of_ne_zero hnext)

theorem gap23 (y : ℝ) (hy : ¬ isNonnegativeInteger y) :
    Asymptotics.IsBigO atTop (boundaryRemainder y)
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  exact gap16 y hy

theorem gap24 (y : ℝ) (hy : -1 / 2 < y) :
    0 < y + 1 / 2 := by linarith

theorem gap25 (y : ℝ) (hy0 : ¬ isNonnegativeInteger y)
    (hy1 : -1 / 2 < y) (hy2 : y ≤ 1 / 2) :
    ∀ᶠ n : ℕ in atTop, 1 < ratioAbs 1 y (n + 1) := by
  have ha : 0 < y + 1 / 2 := gap24 y hy1
  rcases Asymptotics.isBigO_iff.mp (gap23 y hy0) with ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (|C| / (y + 1 / 2))
  filter_upwards [hC, eventually_ge_atTop N] with n hrem hn
  let R : ℝ := ((n + 1 : ℕ) : ℝ)
  have hR : 0 < R := by dsimp [R]; positivity
  have hg : 0 < 1 / R ^ 2 := by positivity
  have hremAbs : |boundaryRemainder y n| ≤ |C| * (1 / R ^ 2) := by
    calc
      |boundaryRemainder y n| = ‖boundaryRemainder y n‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ C * ‖(1 / (((n + 1 : ℕ) : ℝ) ^ 2) : ℝ)‖ := hrem
      _ = C * (1 / R ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_pos hg]
      _ ≤ |C| * (1 / R ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hg.le
  have hremLower : -(|C| * (1 / R ^ 2)) ≤ boundaryRemainder y n := by
    linarith [neg_abs_le (boundaryRemainder y n)]
  have hsmall : |C| < (y + 1 / 2) * R := by
    have hCN : |C| < (y + 1 / 2) * (N : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ ha).mp hN
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [R]
    push_cast
    nlinarith
  have hdom : |C| * (1 / R ^ 2) < (y + 1 / 2) / R := by
    field_simp [hR.ne']
    nlinarith
  unfold boundaryRemainder at hremLower
  dsimp [R] at hdom hremLower
  linarith

theorem gap26 (y : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      |term 1 y n| =
        (Real.exp 1) ^ n * |fallingFactorial y n| / (n : ℝ) ^ n := by
  intro n hn
  unfold term
  simp only [mul_one, abs_div, abs_mul, abs_pow]
  rw [abs_of_pos (Real.exp_pos 1),
    abs_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hn) : (0 : ℝ) < (n : ℝ))]

theorem gap27 (y : ℝ) (hy : -1 / 2 < y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, |term 1 y (n + 1)| ≤ C * boundaryComparison y (n + 1) := by
  by_cases hy0 : isNonnegativeInteger y
  · rcases hy0 with ⟨m, hm⟩
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [eventually_ge_atTop m] with n hn
    have hz : term 1 y (n + 1) = 0 :=
      gap2 1 y m (n + 1) hm (by omega)
    rw [hz, abs_zero, one_mul]
    unfold boundaryComparison
    exact Real.rpow_nonneg (by positivity) _
  · obtain ⟨c, C, hc, hC, hbounds⟩ := term_boundary_comparison y hy0
    exact ⟨C, hC, hbounds.mono (fun n hn => hn.2)⟩

theorem gap28 (y : ℝ) (hy : -1 / 2 < y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, |term 1 y (n + 1)| ≤ C * boundaryComparison y (n + 1) := by
  exact gap27 y hy

theorem gap29 (y : ℝ) (hy : -1 / 2 < y) :
    Tendsto (fun n : ℕ => |term 1 y (n + 1)|) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := gap27 y hy
  have hb := boundaryComparison_tendsto_zero y hy
  have hCb : Tendsto (fun n : ℕ => C * boundaryComparison y (n + 1))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul hb
  apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) hbound hCb

private theorem sign_div_abs_next_of_mul_neg {a b : ℝ} (h : a * b < 0) :
    b / |b| = -(a / |a|) := by
  rcases (mul_neg_iff.mp h) with (⟨ha, hb⟩ | ⟨ha, hb⟩)
  · rw [abs_of_pos ha, abs_of_neg hb]
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hb0 : b ≠ 0 := ne_of_lt hb
    field_simp [ha0, hb0]
  · rw [abs_of_neg ha, abs_of_pos hb]
    have ha0 : a ≠ 0 := ne_of_lt ha
    have hb0 : b ≠ 0 := ne_of_gt hb
    field_simp [ha0, hb0]

theorem gap30 (y : ℝ) (hy0 : ¬ isNonnegativeInteger y)
    (hy1 : -1 / 2 < y) (hy2 : y ≤ 1 / 2) :
    ConditionallySummable 1 y := by
  refine ⟨?_, gap18 1 y (by norm_num) hy0 hy2⟩
  unfold ProofGap.SeriesConverges
  rcases eventually_atTop.1 (gap25 y hy0 hy1 hy2) with ⟨Nr, hNr⟩
  rcases gap22 y hy0 with ⟨Ns, hNs⟩
  let N : ℕ := max Nr Ns
  let u : ℕ → ℝ := fun k => term 1 y (k + N + 1)
  let a : ℕ → ℝ := fun k => |u k|
  have hNrN : Nr ≤ N := le_max_left _ _
  have hNsN : Ns ≤ N := le_max_right _ _
  have haAnti : Antitone a := by
    apply antitone_nat_of_succ_le
    intro k
    have hr := hNr (k + N) (by omega)
    unfold ratioAbs at hr
    rw [abs_div] at hr
    have hden : 0 < |term 1 y (k + N + 2)| :=
      abs_pos.mpr (term_ne_zero one_ne_zero hy0 (k + N + 2) (by omega))
    have hlt := (lt_div_iff₀ hden).mp hr
    dsimp [a, u]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt.le
  have haZero : Tendsto a atTop (𝓝 0) := by
    have h := (gap29 y hy1).comp (tendsto_add_atTop_nat N)
    simpa [a, u, Function.comp_def, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  rcases haAnti.tendsto_alternating_series_of_tendsto_zero haZero with ⟨l, hl⟩
  let s : ℝ := u 0 / |u 0|
  have huNe (k : ℕ) : u k ≠ 0 := by
    dsimp [u]
    exact term_ne_zero one_ne_zero hy0 (k + N + 1) (by omega)
  have hsign : ∀ k : ℕ, u k / |u k| = (-1 : ℝ) ^ k * s := by
    intro k
    induction k with
    | zero => simp [s]
    | succ k ih =>
        have hp : u k * u (k + 1) < 0 := by
          dsimp [u]
          have h := hNs (k + N + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        rw [sign_div_abs_next_of_mul_neg hp, ih, pow_succ]
        ring
  have huEq (k : ℕ) : u k = s * ((-1 : ℝ) ^ k * a k) := by
    have hak : |u k| ≠ 0 := abs_ne_zero.mpr (huNe k)
    calc
      u k = (u k / |u k|) * |u k| := by field_simp [hak]
      _ = ((-1 : ℝ) ^ k * s) * |u k| := by rw [hsign k]
      _ = s * ((-1 : ℝ) ^ k * a k) := by
        dsimp [a]
        ring
  have htail : Tendsto (fun n => ∑ k ∈ Finset.range n, u k)
      atTop (𝓝 (s * l)) := by
    have h := (tendsto_const_nhds (x := s)).mul hl
    convert h using 1
    funext n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact huEq k
  let f : ℕ → ℝ := fun n => term 1 y (n + 1)
  let p : ℝ := ∑ k ∈ Finset.range N, f k
  have hshift : Tendsto (fun n => ∑ k ∈ Finset.range (n + N), f k)
      atTop (𝓝 (p + s * l)) := by
    have h := (tendsto_const_nhds (x := p)).add htail
    convert h using 1
    funext n
    rw [Nat.add_comm n N, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    simp [f, u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hall : Tendsto (fun n => ∑ k ∈ Finset.range n, f k)
      atTop (𝓝 (p + s * l)) := by
    intro V hV
    have hev := hshift hV
    rcases eventually_atTop.1 hev with ⟨K, hK⟩
    refine eventually_atTop.2 ⟨K + N, ?_⟩
    intro m hm
    have hKm : K ≤ m - N := by omega
    have hmN : m - N + N = m := by omega
    simpa [hmN] using hK (m - N) hKm
  refine ⟨p + s * l, ?_⟩
  unfold HasSum
  rw [SummationFilter.conditional_filter_eq_map_range]
  simpa [Function.comp_def, f] using hall

private theorem seriesConverges_tendsto_zero {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) : Tendsto f atTop (𝓝 0) := by
  unfold ProofGap.SeriesConverges at hf
  rcases hf with ⟨l, hl⟩
  unfold HasSum at hl
  rw [SummationFilter.conditional_filter_eq_map_range] at hl
  have hs : Tendsto (fun n => ∑ k ∈ Finset.range n, f k) atTop (𝓝 l) := by
    simpa [Function.comp_def] using hl
  have hs' := hs.comp (tendsto_add_atTop_nat 1)
  have hd := hs'.sub hs
  convert hd using 1
  · funext n
    change f n =
      (∑ k ∈ Finset.range (n + 1), f k) -
        ∑ k ∈ Finset.range n, f k
    rw [Finset.sum_range_succ]
    ring
  · ring

private theorem summable_abs_of_seriesConverges_of_eventually_mul_pos
    {f : ℕ → ℝ} (hf : ProofGap.SeriesConverges f)
    (hprod : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < f n * f (n + 1)) :
    Summable (fun n => |f n|) := by
  unfold ProofGap.SeriesConverges at hf
  rcases hf with ⟨l, hl⟩
  unfold HasSum at hl
  rw [SummationFilter.conditional_filter_eq_map_range] at hl
  have hs : Tendsto (fun n => ∑ k ∈ Finset.range n, f k) atTop (𝓝 l) := by
    simpa [Function.comp_def] using hl
  rcases hprod with ⟨N, hN⟩
  have hNne : f N ≠ 0 := by
    intro hz
    simpa [hz] using (hN N le_rfl).ne'
  have htail : Tendsto (fun n => ∑ k ∈ Finset.range n, f (N + k))
      atTop (𝓝 (l - ∑ k ∈ Finset.range N, f k)) := by
    have hshift := hs.comp (tendsto_add_atTop_nat N)
    have hsub := hshift.sub_const (∑ k ∈ Finset.range N, f k)
    convert hsub using 1
    funext n
    change (∑ k ∈ Finset.range n, f (N + k)) =
      (∑ k ∈ Finset.range (n + N), f k) -
        ∑ k ∈ Finset.range N, f k
    rw [Nat.add_comm n N, Finset.sum_range_add]
    ring
  rcases lt_or_gt_of_ne hNne with hneg | hpos
  · have htailNeg : ∀ k : ℕ, f (N + k) < 0 := by
      intro k
      induction k with
      | zero => simpa using hneg
      | succ k ih =>
          have hp := hN (N + k) (by omega)
          exact neg_of_mul_pos_right hp ih.le
    have htneg : Tendsto (fun n => ∑ k ∈ Finset.range n, -f (N + k))
        atTop (𝓝 (-(l - ∑ k ∈ Finset.range N, f k))) := by
      convert htail.neg using 1
      funext n
      rw [Finset.sum_neg_distrib]
    obtain ⟨C, hC⟩ :=
      (Metric.isBounded_range_of_tendsto _ htneg).bddAbove
    have hsum : Summable (fun k => -f (N + k)) := by
      apply summable_of_sum_range_le
      · intro k
        linarith [htailNeg k]
      · intro n
        exact hC ⟨n, rfl⟩
    have habsShift : Summable (fun k => |f (k + N)|) := by
      apply hsum.congr
      intro k
      rw [abs_of_neg]
      · congr 2
        omega
      · simpa [Nat.add_comm] using htailNeg k
    exact (summable_nat_add_iff N).mp habsShift
  · have htailPos : ∀ k : ℕ, 0 < f (N + k) := by
      intro k
      induction k with
      | zero => simpa using hpos
      | succ k ih =>
          have hp := hN (N + k) (by omega)
          exact pos_of_mul_pos_right hp ih.le
    obtain ⟨C, hC⟩ :=
      (Metric.isBounded_range_of_tendsto _ htail).bddAbove
    have hsum : Summable (fun k => f (N + k)) := by
      apply summable_of_sum_range_le
      · intro k
        exact (htailPos k).le
      · intro n
        exact hC ⟨n, rfl⟩
    have habsShift : Summable (fun k => |f (k + N)|) := by
      apply hsum.congr
      intro k
      rw [Nat.add_comm k N, abs_of_pos (htailPos k)]
    exact (summable_nat_add_iff N).mp habsShift

theorem gap31 :
    {q : ℝ × ℝ |
        Summable (fun n : ℕ => |term q.1 q.2 (n + 1)|)} =
      {q : ℝ × ℝ |
        |q.1| < 1 ∨ (|q.1| = 1 ∧ 1 / 2 < q.2) ∨
          isNonnegativeInteger q.2} := by
  ext q
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hs
    by_cases hy : isNonnegativeInteger q.2
    · exact Or.inr (Or.inr hy)
    rcases lt_trichotomy |q.1| 1 with (hx | hx | hx)
    · exact Or.inl hx
    · refine Or.inr (Or.inl ⟨hx, ?_⟩)
      by_contra hyle
      have hyle' : q.2 ≤ 1 / 2 := le_of_not_gt hyle
      exact gap18 q.1 q.2 hx hy hyle' hs
    · exfalso
      have hnorm : Summable (fun n : ℕ => ‖term q.1 q.2 (n + 1)‖) := by
        simpa [Real.norm_eq_abs] using hs
      have hterm : Summable (fun n : ℕ => term q.1 q.2 (n + 1)) :=
        summable_norm_iff.mp hnorm
      exact gap12 q.1 q.2 hx hy hterm
  · rintro (hx | hx | hy)
    · exact gap10 q.1 q.2 hx
    · exact gap17 q.1 q.2 hx.1 hx.2
    · exact gap3 q.1 q.2 hy

theorem gap32 :
    {q : ℝ × ℝ | ConditionallySummable q.1 q.2} =
      {q : ℝ × ℝ |
        q.1 = 1 ∧ ¬ isNonnegativeInteger q.2 ∧
          -1 / 2 < q.2 ∧ q.2 ≤ 1 / 2} := by
  ext q
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hconv, hnotabs⟩
    have hy0 : ¬ isNonnegativeInteger q.2 := by
      intro hy
      exact hnotabs (gap3 q.1 q.2 hy)
    have hxNotLt : ¬ |q.1| < 1 := by
      intro hx
      exact hnotabs (gap10 q.1 q.2 hx)
    have hxNotGt : ¬ 1 < |q.1| := by
      intro hx
      have hx0 : q.1 ≠ 0 :=
        abs_ne_zero.mp (ne_of_gt (zero_lt_one.trans hx))
      obtain ⟨N, hN⟩ := gap11 q.1 q.2 hx hy0
      let u : ℕ → ℝ := fun k => |term q.1 q.2 (k + N + 1)|
      have huMono : Monotone u := by
        apply monotone_nat_of_le_succ
        intro k
        have hk := hN (k + N + 1) (by omega)
        dsimp [u]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk.le
      have hu0 : 0 < u 0 := by
        dsimp [u]
        exact abs_pos.mpr (by
          simpa using term_ne_zero hx0 hy0 (N + 1) (Nat.succ_ne_zero N))
      have huzero : Tendsto u atTop (𝓝 0) := by
        have h := (seriesConverges_tendsto_zero hconv).abs.comp
          (tendsto_add_atTop_nat N)
        simpa [u, Function.comp_def, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      have hsmall : ∀ᶠ k : ℕ in atTop, u k < u 0 / 2 :=
        (tendsto_order.1 huzero).2 (u 0 / 2) (by linarith)
      rcases eventually_atTop.1 hsmall with ⟨K, hK⟩
      have hlower := huMono (Nat.zero_le K)
      have hupper := hK K le_rfl
      linarith
    have hx : |q.1| = 1 :=
      le_antisymm (le_of_not_gt hxNotGt) (le_of_not_gt hxNotLt)
    have hy1 : -1 / 2 < q.2 := by
      by_contra h
      have hyLe : q.2 ≤ -1 / 2 := le_of_not_gt h
      obtain ⟨c, C, hc, hC, hbounds⟩ :=
        term_boundary_comparison q.2 hy0
      have habsZero :
          Tendsto (fun n : ℕ => |term q.1 q.2 (n + 1)|)
            atTop (𝓝 0) :=
        by simpa only [abs_zero] using
          (seriesConverges_tendsto_zero hconv).abs
      have hsmall :
          ∀ᶠ n : ℕ in atTop, |term q.1 q.2 (n + 1)| < c / 2 :=
        (tendsto_order.1 habsZero).2 (c / 2) (by linarith)
      rcases eventually_atTop.1 hbounds with ⟨Nb, hNb⟩
      rcases eventually_atTop.1 hsmall with ⟨Ns, hNs⟩
      let n : ℕ := max Nb Ns
      have hb := hNb n (le_max_left Nb Ns)
      have hs := hNs n (le_max_right Nb Ns)
      have hbc : 1 ≤ boundaryComparison q.2 (n + 1) := by
        unfold boundaryComparison
        apply Real.one_le_rpow
        · exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
        · linarith
      have hlow : c ≤ |term q.1 q.2 (n + 1)| := by
        calc
          c = c * 1 := by ring
          _ ≤ c * boundaryComparison q.2 (n + 1) :=
            mul_le_mul_of_nonneg_left hbc hc.le
          _ ≤ |term 1 q.2 (n + 1)| := hb.1
          _ = |term q.1 q.2 (n + 1)| :=
            (abs_term_eq_abs_term_one q.1 q.2 hx (n + 1)).symm
      linarith
    have hy2 : q.2 ≤ 1 / 2 := by
      by_contra h
      have hyGt : 1 / 2 < q.2 := lt_of_not_ge h
      exact hnotabs (gap17 q.1 q.2 hx hyGt)
    have hxSq : q.1 ^ 2 = 1 := by
      rw [← sq_abs, hx]
      norm_num
    rcases sq_eq_one_iff.mp hxSq with hxOne | hxNegOne
    · exact ⟨hxOne, hy0, hy1, hy2⟩
    · exfalso
      have hconvNeg :
          ProofGap.SeriesConverges
            (fun n : ℕ => term (-1) q.2 (n + 1)) := by
        simpa [hxNegOne] using hconv
      obtain ⟨N, hN⟩ := gap19 q.2 hy0 hy1 hy2
      have hprod :
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            0 < term (-1) q.2 (n + 1) * term (-1) q.2 (n + 1 + 1) := by
        refine ⟨N, ?_⟩
        intro n hn
        simpa [Nat.add_assoc] using hN (n + 1) (by omega)
      have habsNeg :
          Summable (fun n : ℕ => |term (-1) q.2 (n + 1)|) :=
        summable_abs_of_seriesConverges_of_eventually_mul_pos hconvNeg hprod
      apply hnotabs
      simpa [hxNegOne] using habsNeg
  · rintro ⟨hx, hy0, hy1, hy2⟩
    rw [hx]
    exact gap30 q.2 hy0 hy1 hy2

end

end ProofGap.Exercise2739_3
