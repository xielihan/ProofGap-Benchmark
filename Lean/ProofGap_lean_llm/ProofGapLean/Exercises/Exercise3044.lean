import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace ProofGap.Exercise3044

noncomputable section

open scoped BigOperators Interval

def reciprocalSelfPower (x : ℝ) : ℝ :=
  1 / Real.rpow x x

def exponentialIntegrand (x : ℝ) : ℝ :=
  Real.exp (-x * Real.log x)

def exponentialSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    (-1 : ℝ) ^ n / (n.factorial : ℝ) *
      x ^ n * Real.log x ^ n

def sophomoreSeries : ℝ :=
  ∑' n : ℕ,
    1 / (((n + 1 : ℕ) : ℝ) ^ (n + 1))

private def logMomentPoly (n : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.monomial j
      (1 / ((j.factorial : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (n - j + 1))))

private theorem coeff_finset_sum (s : Finset ℕ) (f : ℕ → Polynomial ℝ) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

private theorem logMomentPoly_identity (n : ℕ) :
    Polynomial.C (((n + 1 : ℕ) : ℝ)) * logMomentPoly n -
        (logMomentPoly n).derivative =
      Polynomial.monomial n (1 / (n.factorial : ℝ)) := by
  ext k
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative]
  unfold logMomentPoly
  rw [coeff_finset_sum, coeff_finset_sum]
  simp [Polynomial.coeff_monomial]
  rcases lt_trichotomy k n with hkn | rfl | hnk
  · rw [if_pos hkn.le, if_pos hkn, if_neg (Nat.ne_of_gt hkn)]
    have hexp : n - k + 1 = (n - (k + 1) + 1) + 1 := by omega
    rw [hexp, pow_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · simp
    field_simp
  · rw [if_neg (not_le_of_gt hnk), if_neg (not_lt_of_ge hnk.le),
      if_neg (Nat.ne_of_lt hnk)]
    simp

private def logMomentPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (n + 1) * (logMomentPoly n).eval (-Real.log x)

private theorem hasDerivAt_logMomentPrimitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logMomentPrimitive n)
      ((-1 : ℝ) ^ n / (n.factorial : ℝ) * x ^ n * Real.log x ^ n) x := by
  let q := logMomentPoly n
  let t := -Real.log x
  have ht : HasDerivAt (fun y : ℝ => -Real.log y) (-1 / x) x := by
    convert (Real.hasDerivAt_log hx.ne').neg using 1 <;> field_simp
  have hq : HasDerivAt (fun y : ℝ => q.eval (-Real.log y))
      (q.derivative.eval t * (-1 / x)) x := by
    exact (q.hasDerivAt_aeval t).comp x ht
  have hp : HasDerivAt (fun y : ℝ => y ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * x ^ n) x := by
    convert hasDerivAt_pow (n + 1) x using 1 <;> push_cast <;> ring
  have hprod := hp.mul hq
  have hid := congrArg (fun p : Polynomial ℝ => p.eval t) (logMomentPoly_identity n)
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_monomial, one_mul] at hid
  have halg :
      (((n + 1 : ℕ) : ℝ) * x ^ n) * q.eval t +
          x ^ (n + 1) * (q.derivative.eval t * (-1 / x)) =
        (-1 : ℝ) ^ n / (n.factorial : ℝ) * x ^ n * Real.log x ^ n := by
    have hidq : (((n + 1 : ℕ) : ℝ) * q.eval t - q.derivative.eval t) =
        1 / (n.factorial : ℝ) * t ^ n := by simpa [q] using hid
    calc
      (((n + 1 : ℕ) : ℝ) * x ^ n) * q.eval t +
          x ^ (n + 1) * (q.derivative.eval t * (-1 / x)) =
          x ^ n * ((((n + 1 : ℕ) : ℝ) * q.eval t) -
            q.derivative.eval t) := by
        rw [pow_succ]
        field_simp [hx.ne']
        ring
      _ = x ^ n * (1 / (n.factorial : ℝ) * t ^ n) := by rw [hidq]
      _ = (-1 : ℝ) ^ n / (n.factorial : ℝ) * x ^ n * Real.log x ^ n := by
        dsimp [t]
        rw [neg_pow]
        ring
  simpa only [logMomentPrimitive, q, t] using hprod.congr_deriv halg

private theorem logMomentPrimitive_eq_sum (n : ℕ) (x : ℝ) :
    logMomentPrimitive n x =
      ∑ j ∈ Finset.range (n + 1),
        (1 / ((j.factorial : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (n - j + 1)))) *
          (x ^ (n + 1 - j) * (-(x * Real.log x)) ^ j) := by
  unfold logMomentPrimitive logMomentPoly
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hadd : n + 1 - j + j = n + 1 := Nat.sub_add_cancel (Nat.le_succ_of_le hjle)
  rw [show -(x * Real.log x) = x * (-Real.log x) by ring,
    mul_pow]
  have hpow : x ^ (n + 1 - j) * x ^ j = x ^ (n + 1) := by
    rw [← pow_add, hadd]
  rw [← hpow]
  ring

private theorem continuous_logMomentPrimitive (n : ℕ) :
    Continuous (logMomentPrimitive n) := by
  rw [funext (logMomentPrimitive_eq_sum n)]
  fun_prop

private theorem continuous_logMomentIntegrand (n : ℕ) :
    Continuous (fun x : ℝ =>
      (-1 : ℝ) ^ n / (n.factorial : ℝ) * x ^ n * Real.log x ^ n) := by
  have heq :
      (fun x : ℝ =>
        (-1 : ℝ) ^ n / (n.factorial : ℝ) * x ^ n * Real.log x ^ n) =
      (fun x : ℝ =>
        ((-1 : ℝ) ^ n / (n.factorial : ℝ)) * (x * Real.log x) ^ n) := by
    funext x
    rw [mul_pow]
    ring
  rw [heq]
  exact continuous_const.mul (Real.continuous_mul_log.pow n)

private theorem logMomentPrimitive_zero (n : ℕ) :
    logMomentPrimitive n 0 = 0 := by
  simp [logMomentPrimitive]

private theorem logMomentPrimitive_one (n : ℕ) :
    logMomentPrimitive n 1 =
      1 / (((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by
  simp only [logMomentPrimitive, one_pow, Real.log_one, neg_zero,
    logMomentPoly, Polynomial.eval_finset_sum, Polynomial.eval_monomial, one_mul]
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro j hj hj0
    rw [zero_pow hj0]
    ring
  · simp

private theorem negMulLog_le_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.negMulLog x ≤ 1 := by
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
  rw [Real.log_inv] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hx0.le
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
  rw [mul_sub, hinv] at hm
  unfold Real.negMulLog
  nlinarith

private theorem hasSum_logMomentIntegrals :
    HasSum
      (fun n : ℕ => ∫ x in (0 : ℝ)..1,
        (-1 : ℝ) ^ n / (n.factorial : ℝ) * x ^ n * Real.log x ^ n)
      (∫ x in (0 : ℝ)..1, exponentialIntegrand x) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n : ℕ => fun _ : ℝ => 1 / (n.factorial : ℝ))
  · intro n
    exact (continuous_logMomentIntegrand n).aestronglyMeasurable
  · intro n
    filter_upwards with x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hneg0 : 0 ≤ Real.negMulLog x :=
      Real.negMulLog_nonneg hx.1.le hx.2
    have hneg1 : Real.negMulLog x ≤ 1 := negMulLog_le_one hx.1 hx.2
    have hpow : Real.negMulLog x ^ n ≤ 1 := pow_le_one₀ hneg0 hneg1
    have heq :
        (-1 : ℝ) ^ n / (n.factorial : ℝ) * x ^ n * Real.log x ^ n =
          Real.negMulLog x ^ n / (n.factorial : ℝ) := by
      unfold Real.negMulLog
      rw [show -x * Real.log x = (-1 : ℝ) * x * Real.log x by ring,
        mul_pow, mul_pow]
      ring
    rw [heq, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (pow_nonneg hneg0 n) (by positivity))]
    exact div_le_div_of_nonneg_right hpow (by positivity)
  · filter_upwards with x hx
    simpa [one_pow] using (Real.summable_pow_div_factorial 1)
  · exact intervalIntegrable_const
  · filter_upwards with x hx
    unfold exponentialIntegrand
    have hs : HasSum (fun n : ℕ => (-x * Real.log x) ^ n / (n.factorial : ℝ))
        (Real.exp (-x * Real.log x)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (-x * Real.log x)
    have hfun :
        (fun n : ℕ => (-1 : ℝ) ^ n / (n.factorial : ℝ) *
          x ^ n * Real.log x ^ n) =
        (fun n : ℕ => (-x * Real.log x) ^ n / (n.factorial : ℝ)) := by
      funext n
      rw [show -x * Real.log x = (-1 : ℝ) * x * Real.log x by ring,
        mul_pow, mul_pow]
      ring
    rw [hfun]
    exact hs

theorem gap1 :
    (∫ x in (0 : ℝ)..1, reciprocalSelfPower x) =
      ∫ x in (0 : ℝ)..1, exponentialIntegrand x := by
  apply intervalIntegral.integral_congr
  intro x hx
  unfold reciprocalSelfPower exponentialIntegrand
  have hx0 : 0 ≤ x := by
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact hx.1
  obtain rfl | hxpos := hx0.eq_or_lt
  · norm_num
  change 1 / (x ^ x : ℝ) = Real.exp (-x * Real.log x)
  rw [Real.rpow_def_of_pos hxpos, one_div, ← Real.exp_neg]
  congr 1
  ring

theorem gap2 :
    (∫ x in (0 : ℝ)..1, exponentialIntegrand x) =
      ∫ x in (0 : ℝ)..1, exponentialSeries x := by
  apply intervalIntegral.integral_congr
  intro x hx
  unfold exponentialIntegrand exponentialSeries
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  apply tsum_congr
  intro n
  field_simp
  rw [neg_pow, mul_pow]
  ring

theorem gap3 (n : ℕ) :
    (∫ x in (0 : ℝ)..1,
      (-1 : ℝ) ^ n / (n.factorial : ℝ) *
        x ^ n * Real.log x ^ n) =
      1 / (((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := logMomentPrimitive n) (fa := 0)
    (fb := 1 / (((n + 1 : ℕ) : ℝ) ^ (n + 1)))
    (hint := (continuous_logMomentIntegrand n).intervalIntegrable 0 1)]
  · ring
  · norm_num
  · intro x hx
    exact hasDerivAt_logMomentPrimitive n hx.1
  · have ht : Filter.Tendsto (logMomentPrimitive n) (nhds (0 : ℝ))
        (nhds (logMomentPrimitive n 0)) :=
      (continuous_logMomentPrimitive n).continuousAt.tendsto
    have hw : Filter.Tendsto (logMomentPrimitive n)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (logMomentPrimitive n 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds ht
    simpa only [logMomentPrimitive_zero n] using hw
  · have ht : Filter.Tendsto (logMomentPrimitive n) (nhds (1 : ℝ))
        (nhds (logMomentPrimitive n 1)) :=
      (continuous_logMomentPrimitive n).continuousAt.tendsto
    have hw : Filter.Tendsto (logMomentPrimitive n)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (logMomentPrimitive n 1)) :=
      tendsto_nhdsWithin_of_tendsto_nhds ht
    simpa only [logMomentPrimitive_one n] using hw

theorem gap4 :
    (∫ x in (0 : ℝ)..1, reciprocalSelfPower x) =
      sophomoreSeries := by
  calc
    (∫ x in (0 : ℝ)..1, reciprocalSelfPower x) =
        ∫ x in (0 : ℝ)..1, exponentialIntegrand x := gap1
    _ = ∑' n : ℕ, ∫ x in (0 : ℝ)..1,
          (-1 : ℝ) ^ n / (n.factorial : ℝ) *
            x ^ n * Real.log x ^ n := hasSum_logMomentIntegrals.tsum_eq.symm
    _ = sophomoreSeries := by
      unfold sophomoreSeries
      apply tsum_congr
      intro n
      exact gap3 n

theorem gap5 :
    sophomoreSeries =
      ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by
  rfl

theorem gap6 :
    (∫ x in (0 : ℝ)..1, reciprocalSelfPower x) =
      ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by
  exact gap4

theorem gap7 :
    (∫ x in (0 : ℝ)..1, reciprocalSelfPower x) =
      ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by
  exact gap6

end

end ProofGap.Exercise3044
