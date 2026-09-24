import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2542

noncomputable section

def taylorExp (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), x ^ k / k.factorial
def expRemainder (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp x - taylorExp n x
def logMoment (k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ k * Real.log (1 / x)
def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, (Real.exp x - 1) * Real.log (1 / x)
def seriesApprox (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (1 / k.factorial : ℝ) * logMoment k
def seriesRemainder (n : ℕ) : ℝ := targetIntegral - seriesApprox n
def roundingError : ℝ := seriesApprox 5 - 0.3179
def combinedError : ℝ := seriesRemainder 5 + roundingError
def g (x : ℝ) : ℝ := if x = 0 then 1 else (Real.exp x - 1) / x
def f (x : ℝ) : ℝ := if x = 0 then 0 else (Real.exp x - 1) * Real.log x
def nthDeriv (n : ℕ) (u : ℝ → ℝ) : ℝ → ℝ := deriv^[n] u
def P (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * (-1 : ℝ) ^ k * k.factorial * x ^ (n - k)
def fourthDerivG (x : ℝ) : ℝ := nthDeriv 4 g x
def simpsonG : ℝ :=
  1 / 12 * (g 0 + g 1 + 2 * g (1 / 2) +
    4 * (g (1 / 4) + g (3 / 4)))
def simpsonRemainderG : ℝ :=
  (∫ x in (0 : ℝ)..1, g x) - simpsonG

private theorem taylorExp_zero (n : ℕ) : taylorExp n 0 = 1 := by
  unfold taylorExp
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro b hb hb0
    simp [hb0]
  · simp

private theorem continuous_g : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hg : g = Function.update (fun y : ℝ => (Real.exp y - 1) / y) 0 1 := by
      funext y
      simp [g, Function.update]
    rw [hg]
    simpa only [Real.exp_zero, sub_zero] using
      (Real.hasDerivAt_exp 0).continuousAt_div
  · have hq : ContinuousAt (fun y : ℝ => (Real.exp y - 1) / y) x :=
      (Real.continuous_exp.continuousAt.sub continuousAt_const).div continuousAt_id hx
    apply hq.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [g, hy]

private theorem continuous_f : Continuous f := by
  have hf : f = fun x => g x * (x * Real.log x) := by
    funext x
    by_cases hx : x = 0
    · simp [f, g, hx]
    · simp only [f, g, if_neg hx]
      field_simp
  rw [hf]
  exact continuous_g.mul Real.continuous_mul_log

private def expMoment (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ n * Real.exp (t * x)

private theorem expMoment_zero (n : ℕ) : expMoment n 0 = 1 / (n + 1 : ℝ) := by
  unfold expMoment
  simp [integral_pow]

private theorem g_eq_expMoment_zero : g = expMoment 0 := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [g, expMoment]
  · rw [g, if_neg hx]
    unfold expMoment
    simp only [pow_zero, one_mul]
    have hfun : (fun t : ℝ => Real.exp (t * x)) = (fun t : ℝ => Real.exp (x * t)) := by
      funext t
      rw [mul_comm]
    rw [hfun]
    rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) hx]
    simp [smul_eq_mul, integral_exp, Real.exp_zero]
    ring

private theorem expMoment_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (expMoment n) (expMoment (n + 1) x) x := by
  let C : ℝ := Real.exp (|x| + 1)
  let s : Set ℝ := Set.Icc (x - 1) (x + 1)
  have hs : s ∈ nhds x := by
    dsimp [s]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
    (F := fun z t : ℝ => t ^ n * Real.exp (t * z))
    (F' := fun z t : ℝ => t ^ (n + 1) * Real.exp (t * z))
    (s := s) (bound := fun _ : ℝ => C) hs
    (Filter.Eventually.of_forall fun z =>
      (by fun_prop : Continuous fun t : ℝ => t ^ n * Real.exp (t * z))
        |>.aestronglyMeasurable.restrict)
    ((by fun_prop : Continuous fun t : ℝ => t ^ n * Real.exp (t * x)).intervalIntegrable 0 1)
    ((by fun_prop : Continuous fun t : ℝ => t ^ (n + 1) * Real.exp (t * x))
      |>.aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall fun t ht z hz => by
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htIoc.1.le, htIoc.2⟩
      have hzabs : |z| ≤ |x| + 1 := by
        rcases hz with ⟨hz1, hz2⟩
        rw [abs_le]
        constructor
        · nlinarith [neg_le_abs x]
        · nlinarith [le_abs_self x]
      have htz : t * z ≤ |z| := by
        by_cases hz0 : 0 ≤ z
        · rw [abs_of_nonneg hz0]
          exact mul_le_of_le_one_left hz0 ht'.2
        · exact (mul_nonpos_of_nonneg_of_nonpos ht'.1 (le_of_not_ge hz0)).trans
            (abs_nonneg z)
      have htx : t * z ≤ |x| + 1 := htz.trans hzabs
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ht'.1,
        abs_of_pos (Real.exp_pos _)]
      calc
        t ^ (n + 1) * Real.exp (t * z) ≤ 1 * Real.exp (t * z) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ ht'.1 ht'.2) (Real.exp_pos _).le
        _ ≤ C := by
          dsimp [C]
          simpa only [one_mul] using Real.exp_le_exp.mpr htx)
    ((by fun_prop : Continuous fun _ : ℝ => C).intervalIntegrable 0 1)
    (Filter.Eventually.of_forall fun t ht z hz => by
      have hlin : HasDerivAt (fun y : ℝ => t * y) t z := by
        convert (hasDerivAt_id z).const_mul t using 1 <;> simp
      have he : HasDerivAt (fun y : ℝ => Real.exp (t * y)) (Real.exp (t * z) * t) z :=
        (Real.hasDerivAt_exp (t * z)).comp z hlin
      convert he.const_mul (t ^ n) using 1 <;> simp [pow_succ] <;> ring)
  simpa [expMoment] using h.2

private theorem nthDeriv_g_eq_expMoment (n : ℕ) : nthDeriv n g = expMoment n := by
  induction n with
  | zero => simpa [nthDeriv] using g_eq_expMoment_zero
  | succ n ih =>
      unfold nthDeriv at ih ⊢
      rw [Function.iterate_succ_apply', ih]
      funext x
      exact (expMoment_hasDerivAt n x).deriv

private theorem continuous_nthDeriv_g (n : ℕ) : Continuous (nthDeriv n g) := by
  rw [nthDeriv_g_eq_expMoment n]
  rw [continuous_iff_continuousAt]
  exact fun x => (expMoment_hasDerivAt n x).continuousAt

theorem gap1 (n : ℕ) (x : ℝ) :
    Real.exp x = taylorExp n x + expRemainder n x := by
  unfold expRemainder
  ring
theorem gap2 (n : ℕ) (x : ℝ) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      expRemainder n x =
        Real.exp (θ * x) / (n + 1).factorial * x ^ (n + 1) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · let q : ℝ → ℝ := fun s => Real.exp ((-1 : ℝ) * s)
    have hz : 0 < -x := neg_pos.mpr hx
    obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := q) (n := n) hz
        (by dsimp [q]; fun_prop)
    have ht : taylorWithinEval q n (Set.Icc 0 (-x)) 0 (-x) = taylorExp n x := by
      rw [taylor_within_apply]
      unfold taylorExp
      apply Finset.sum_congr rfl
      intro j hj
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hz)
        (by dsimp [q]; fun_prop) (by exact ⟨le_rfl, hz.le⟩)]
      dsimp [q]
      rw [iteratedDeriv_exp_const_mul]
      simp only [mul_zero, Real.exp_zero, mul_one, sub_zero]
      rw [neg_pow]
      have hs : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (↑j.factorial)⁻¹ * ((-1 : ℝ) ^ j * x ^ j) * (-1 : ℝ) ^ j =
            (↑j.factorial)⁻¹ * x ^ j * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) := by ring
        _ = (↑j.factorial)⁻¹ * x ^ j := by rw [hs, mul_one]
        _ = x ^ j / ↑j.factorial := by ring
    rw [ht] at hrem
    have hi : iteratedDeriv (n + 1) q y =
        (-1 : ℝ) ^ (n + 1) * Real.exp ((-1 : ℝ) * y) := by
      dsimp [q]
      rw [iteratedDeriv_exp_const_mul]
    rw [hi] at hrem
    refine ⟨y / (-x), ⟨div_pos hy.1 hz, (div_lt_one hz).2 hy.2⟩, ?_⟩
    have hθx : y / (-x) * x = -y := by
      field_simp [hx.ne]
    have hsign : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    unfold expRemainder
    rw [hθx]
    calc
      Real.exp x - taylorExp n x =
          ((-1 : ℝ) ^ (n + 1) * Real.exp ((-1 : ℝ) * y)) *
            (-x) ^ (n + 1) / (n + 1).factorial := by
              simpa [q] using hrem
      _ = Real.exp (-y) / (n + 1).factorial * x ^ (n + 1) := by
        nth_rewrite 2 [neg_pow]
        rw [show ((-1 : ℝ) ^ (n + 1) * Real.exp ((-1 : ℝ) * y)) *
              ((-1 : ℝ) ^ (n + 1) * x ^ (n + 1)) =
              Real.exp (-y) * x ^ (n + 1) by
          calc
            _ = ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) *
                (Real.exp ((-1 : ℝ) * y) * x ^ (n + 1)) := by ring
            _ = Real.exp (-y) * x ^ (n + 1) := by rw [hsign, one_mul]; ring]
        ring
  · refine ⟨1 / 2, by norm_num, ?_⟩
    simp [expRemainder, taylorExp_zero, Nat.succ_ne_zero]
  · obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.exp) (n := n) hx
        Real.contDiff_exp.contDiffOn
    have ht : taylorWithinEval Real.exp n (Set.Icc 0 x) 0 x = taylorExp n x := by
      rw [taylor_within_apply]
      unfold taylorExp
      apply Finset.sum_congr rfl
      intro j hj
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
        Real.contDiff_exp.contDiffAt (by exact ⟨le_rfl, hx.le⟩)]
      rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
      simp only [smul_eq_mul, sub_zero, mul_one, Real.exp_zero]
      ring
    rw [ht] at hrem
    have hi : iteratedDeriv (n + 1) Real.exp y = Real.exp y := by
      rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
    rw [hi] at hrem
    refine ⟨y / x, ⟨div_pos hy.1 hx, (div_lt_one hx).2 hy.2⟩, ?_⟩
    have hθx : y / x * x = y := div_mul_cancel₀ y hx.ne'
    unfold expRemainder
    rw [hθx, hrem]
    ring
theorem gap3 (n : ℕ) (x θ : ℝ) :
    Real.exp (θ * x) / (n + 1).factorial * x ^ (n + 1) =
      Real.exp (θ * x) / (n + 1).factorial * x ^ (n + 1) := by
  rfl
theorem gap4 (n : ℕ) (x : ℝ) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      expRemainder n x =
        Real.exp (θ * x) / (n + 1).factorial * x ^ (n + 1) := by
  exact gap2 n x
theorem gap5 (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |expRemainder n x| ≤
      Real.exp 1 / (n + 1).factorial * x ^ (n + 1) := by
  obtain ⟨θ, hθ, hrem⟩ := gap2 n x
  rw [hrem, abs_of_nonneg]
  · apply mul_le_mul_of_nonneg_right
    · exact div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (by nlinarith [hθ.1, hθ.2, hx.1, hx.2])) (by positivity)
    · exact pow_nonneg hx.1 _
  · exact mul_nonneg (div_nonneg (Real.exp_pos _).le (by positivity)) (pow_nonneg hx.1 _)
theorem gap6 (n : ℕ) :
    targetIntegral = seriesApprox n + seriesRemainder n := by
  unfold seriesRemainder
  ring
private theorem seriesRemainder_eq_integral (n : ℕ) :
    seriesRemainder n =
      ∫ x in (0 : ℝ)..1, expRemainder n x * Real.log (1 / x) := by
  let L : ℝ → ℝ := fun x => Real.log (1 / x)
  let tail : ℝ → ℝ := fun x =>
    ∑ k ∈ Finset.Icc (1 : ℕ) n, (1 / k.factorial : ℝ) * x ^ k
  have hlog : IntervalIntegrable L MeasureTheory.volume (0 : ℝ) 1 := by
    have h := intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)
    simpa [L, one_div, Real.log_inv] using h.neg
  have htailc : Continuous tail := by
    dsimp [tail]
    fun_prop
  have hremc : Continuous (expRemainder n) := by
    unfold expRemainder taylorExp
    fun_prop
  have htailint : IntervalIntegrable (fun x => tail x * L x)
      MeasureTheory.volume (0 : ℝ) 1 :=
    hlog.continuousOn_mul htailc.continuousOn
  have hremint : IntervalIntegrable (fun x => expRemainder n x * L x)
      MeasureTheory.volume (0 : ℝ) 1 :=
    hlog.continuousOn_mul hremc.continuousOn
  have htaylor (x : ℝ) : taylorExp n x = 1 + tail x := by
    have hset : Finset.Icc (1 : ℕ) n = (Finset.range (n + 1)).erase 0 := by
      ext k
      simp
      omega
    have hmem : 0 ∈ Finset.range (n + 1) := by simp
    unfold taylorExp
    calc
      (∑ k ∈ Finset.range (n + 1), x ^ k / k.factorial) =
          (∑ k ∈ (Finset.range (n + 1)).erase 0, x ^ k / k.factorial) +
            0 ^ 0 / Nat.factorial 0 :=
        ((Finset.range (n + 1)).sum_erase_add
          (fun k => x ^ k / (k.factorial : ℝ)) hmem).symm
      _ = 1 + tail x := by
        rw [← hset]
        dsimp [tail]
        norm_num
        rw [add_comm (∑ k ∈ Finset.Icc (1 : ℕ) n, x ^ k / (k.factorial : ℝ)) 1]
        apply congrArg (fun z : ℝ => 1 + z)
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hseries : seriesApprox n = ∫ x in (0 : ℝ)..1, tail x * L x := by
    unfold seriesApprox logMoment
    calc
      (∑ k ∈ Finset.Icc 1 n,
          (1 / k.factorial : ℝ) * (∫ x in (0 : ℝ)..1, x ^ k * Real.log (1 / x))) =
          ∑ k ∈ Finset.Icc 1 n,
            (∫ x in (0 : ℝ)..1,
              (1 / k.factorial : ℝ) * (x ^ k * Real.log (1 / x))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ x in (0 : ℝ)..1,
          ∑ k ∈ Finset.Icc 1 n,
            (1 / k.factorial : ℝ) * (x ^ k * Real.log (1 / x)) := by
        rw [intervalIntegral.integral_finset_sum]
        intro k hk
        exact (hlog.continuousOn_mul (continuousOn_id.pow k)).const_mul _
      _ = ∫ x in (0 : ℝ)..1, tail x * L x := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [tail, L]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have htarget : targetIntegral =
      (∫ x in (0 : ℝ)..1, tail x * L x) +
        (∫ x in (0 : ℝ)..1, expRemainder n x * L x) := by
    unfold targetIntegral
    rw [← intervalIntegral.integral_add htailint hremint]
    apply intervalIntegral.integral_congr
    intro x hx
    have ht := htaylor x
    dsimp [L]
    unfold expRemainder
    rw [ht]
    ring
  have hremainder : seriesRemainder n =
      ∫ x in (0 : ℝ)..1, expRemainder n x * Real.log (1 / x) := by
    unfold seriesRemainder
    rw [htarget, hseries]
    dsimp [L]
    ring
  exact hremainder

theorem gap7 (n : ℕ) :
    |seriesRemainder n| =
      |∫ x in (0 : ℝ)..1, expRemainder n x * Real.log (1 / x)| := by
  rw [seriesRemainder_eq_integral]
theorem gap8 (n : ℕ) :
    |∫ x in (0 : ℝ)..1, expRemainder n x * Real.log (1 / x)| ≤
      Real.exp 1 / (n + 1).factorial * logMoment (n + 1) := by
  let L : ℝ → ℝ := fun x => Real.log (1 / x)
  let C : ℝ := Real.exp 1 / (n + 1).factorial
  have hlog : IntervalIntegrable L MeasureTheory.volume (0 : ℝ) 1 := by
    have h := intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)
    simpa [L, one_div, Real.log_inv] using h.neg
  have hremc : Continuous (expRemainder n) := by
    unfold expRemainder taylorExp
    fun_prop
  have hremint : IntervalIntegrable (fun x => expRemainder n x * L x)
      MeasureTheory.volume (0 : ℝ) 1 :=
    hlog.continuousOn_mul hremc.continuousOn
  have huppint : IntervalIntegrable (fun x => C * (x ^ (n + 1) * L x))
      MeasureTheory.volume (0 : ℝ) 1 :=
    (hlog.continuousOn_mul (continuousOn_id.pow (n + 1))).const_mul C
  calc
    |∫ x in (0 : ℝ)..1, expRemainder n x * Real.log (1 / x)| ≤
        ∫ x in (0 : ℝ)..1, |expRemainder n x * L x| := by
      simpa [L] using intervalIntegral.abs_integral_le_integral_abs
        (f := fun x => expRemainder n x * L x) (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ ∫ x in (0 : ℝ)..1, C * (x ^ (n + 1) * L x) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hremint.abs huppint
      intro x hx
      have hL : 0 ≤ L x := by
        dsimp [L]
        rw [one_div, Real.log_inv]
        exact neg_nonneg.mpr (Real.log_nonpos hx.1 hx.2)
      rw [abs_mul, abs_of_nonneg hL]
      dsimp [C]
      calc
        |expRemainder n x| * L x ≤
            (Real.exp 1 / (n + 1).factorial * x ^ (n + 1)) * L x :=
          mul_le_mul_of_nonneg_right (gap5 n x hx) hL
        _ = Real.exp 1 / (n + 1).factorial * (x ^ (n + 1) * L x) := by ring
    _ = Real.exp 1 / (n + 1).factorial * logMoment (n + 1) := by
      dsimp [C, L]
      rw [intervalIntegral.integral_const_mul]
      rfl
theorem gap9 (n : ℕ) :
    |seriesRemainder n| ≤
      Real.exp 1 / (n + 1).factorial * logMoment (n + 1) := by
  rw [gap7 n]
  exact gap8 n
theorem gap10 (k : ℕ) :
    logMoment k =
      1 / (k + 1 : ℝ) *
        (∫ x in (0 : ℝ)..1, Real.log (1 / x) * ((k + 1) * x ^ k)) := by
  unfold logMoment
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp
theorem gap11 (k : ℕ) :
    logMoment k =
      1 / (k + 1 : ℝ) * (∫ x in (0 : ℝ)..1, x ^ k) := by
  let m : ℕ := k + 1
  let c : ℝ := k + 1
  let F : ℝ → ℝ := fun x =>
    -(x ^ m * Real.log (x ^ m)) / c ^ 2 + x ^ m / c ^ 2
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (x ^ k * Real.log (1 / x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hpow : HasDerivAt (fun y : ℝ => y ^ m)
        ((m : ℝ) * x ^ (m - 1)) x := by
      simpa using (hasDerivAt_id x).pow m
    have hlog := hpow.log (pow_ne_zero m hx0)
    have hmul := hpow.mul hlog
    have hF := (hmul.neg.div_const (c ^ 2)).add (hpow.div_const (c ^ 2))
    convert hF using 1
    dsimp [m, c]
    rw [one_div, Real.log_inv, Real.log_pow]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    field_simp <;> ring
  have hint : IntervalIntegrable (fun x : ℝ => x ^ k * Real.log (1 / x))
      MeasureTheory.volume 0 1 := by
    have hlog : IntervalIntegrable Real.log MeasureTheory.volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_log'
    have hmul := hlog.continuousOn_mul (continuousOn_id.pow k)
    simpa [one_div, Real.log_inv] using hmul.neg
  have hFTC : (∫ x in (0 : ℝ)..1, x ^ k * Real.log (1 / x)) = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont.continuousOn
      hderiv hint
  unfold logMoment
  rw [hFTC, integral_pow]
  dsimp [F, m, c]
  simp only [one_pow, Real.log_one, mul_zero, neg_zero, zero_div,
    zero_pow (Nat.succ_ne_zero k), Real.log_zero, sub_zero]
  field_simp
  ring
theorem gap12 (k : ℕ) :
    (1 / (k + 1 : ℝ)) * (∫ x in (0 : ℝ)..1, x ^ k) =
      1 / (k + 1 : ℝ) ^ 2 := by
  rw [integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp <;> ring
theorem gap13 (k : ℕ) :
    logMoment k = 1 / (k + 1 : ℝ) ^ 2 := by
  calc
    logMoment k = 1 / (k + 1 : ℝ) * (∫ x in (0 : ℝ)..1, x ^ k) := gap11 k
    _ = 1 / (k + 1 : ℝ) ^ 2 := gap12 k
theorem gap14 :
    |seriesRemainder 5| ≤ Real.exp 1 / Nat.factorial 6 * logMoment 6 := by
  simpa using gap9 5
theorem gap15 :
    Real.exp 1 / Nat.factorial 6 * logMoment 6 =
      Real.exp 1 / Nat.factorial 6 * (1 / (7 : ℝ) ^ 2) := by
  rw [gap13 6]
  norm_num
theorem gap16 :
    Real.exp 1 / Nat.factorial 6 * (1 / (7 : ℝ) ^ 2) =
      Real.exp 1 / (7 * Nat.factorial 7) := by
  norm_num [Nat.factorial]
  ring
theorem gap17 :
    Real.exp 1 / (7 * Nat.factorial 7) = Real.exp 1 / 35280 := by
  norm_num [Nat.factorial]
theorem gap18 : Real.exp 1 / 35280 < 3 / 35280 := by
  exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 35280)).2
    Real.exp_one_lt_three
theorem gap19 : (3 / 35280 : ℝ) < 1 / (1.1 * 10 ^ 4) := by
  norm_num
theorem gap20 : (1 / (1.1 * 10 ^ 4) : ℝ) < 10 ^ (-4 : ℤ) := by
  norm_num
theorem gap21 : |seriesRemainder 5| < 10 ^ (-4 : ℤ) := by
  calc
    |seriesRemainder 5| ≤ Real.exp 1 / Nat.factorial 6 * logMoment 6 := gap14
    _ = Real.exp 1 / Nat.factorial 6 * (1 / (7 : ℝ) ^ 2) := gap15
    _ = Real.exp 1 / (7 * Nat.factorial 7) := gap16
    _ = Real.exp 1 / 35280 := gap17
    _ < 3 / 35280 := gap18
    _ < 1 / (1.1 * 10 ^ 4) := gap19
    _ < 10 ^ (-4 : ℤ) := gap20
theorem gap22 : seriesApprox 5 = seriesApprox 5 := by
  rfl
theorem gap23 :
    seriesApprox 5 =
      ∑ k ∈ Finset.Icc (1 : ℕ) 5,
        (1 / k.factorial : ℝ) * (1 / (k + 1 : ℝ) ^ 2) := by
  unfold seriesApprox
  apply Finset.sum_congr rfl
  intro k hk
  rw [gap13 k]
theorem gap24 :
    (∑ k ∈ Finset.Icc (1 : ℕ) 5,
      (1 / k.factorial : ℝ) * (1 / (k + 1 : ℝ) ^ 2)) =
      ∑ k ∈ Finset.Icc (1 : ℕ) 5,
        1 / (((k + 1).factorial : ℝ) * (k + 1 : ℝ)) := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorial_succ]
  push_cast
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
theorem gap25 :
    seriesApprox 5 =
      ∑ k ∈ Finset.Icc (1 : ℕ) 5,
        1 / (((k + 1).factorial : ℝ) * (k + 1 : ℝ)) := by
  exact (gap23.trans gap24)
theorem gap26 :
    seriesApprox 5 =
      1 / ((Nat.factorial 2 : ℝ) * 2) + 1 / ((Nat.factorial 3 : ℝ) * 3) +
      1 / ((Nat.factorial 4 : ℝ) * 4) + 1 / ((Nat.factorial 5 : ℝ) * 5) +
      1 / ((Nat.factorial 6 : ℝ) * 6) := by
  rw [gap25]
  norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
theorem gap27 :
    (1 / ((Nat.factorial 2 : ℝ) * 2) + 1 / ((Nat.factorial 3 : ℝ) * 3) +
      1 / ((Nat.factorial 4 : ℝ) * 4) + 1 / ((Nat.factorial 5 : ℝ) * 5) +
      1 / ((Nat.factorial 6 : ℝ) * 6)) =
      1 / 4 + 1 / 18 + 1 / 96 + 1 / 600 + 1 / 4320 := by
  norm_num [Nat.factorial]
theorem gap28 :
    |(1 / 4 + 1 / 18 + 1 / 96 + 1 / 600 + 1 / 4320 : ℝ) -
      0.31787| < 0.00001 := by
  norm_num [abs_lt]
theorem gap29 : |seriesApprox 5 - 0.31787| < 0.00001 := by
  rw [gap26, gap27]
  exact gap28
theorem gap30 : |roundingError| ≤ 0.00004 := by
  unfold roundingError
  rw [gap26, gap27]
  norm_num [abs_le]
theorem gap31 : roundingError < 0 := by
  unfold roundingError
  rw [gap26, gap27]
  norm_num
theorem gap32 : 0 < seriesRemainder 5 := by
  rw [seriesRemainder_eq_integral]
  have hlog : IntervalIntegrable (fun x : ℝ => Real.log (1 / x))
      MeasureTheory.volume 0 1 := by
    have h := intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)
    simpa [one_div, Real.log_inv] using h.neg
  have hremc : Continuous (expRemainder 5) := by
    unfold expRemainder taylorExp
    fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (hlog.continuousOn_mul hremc.continuousOn)
  · intro x hx
    obtain ⟨θ, hθ, hrem⟩ := gap2 5 x
    rw [hrem]
    have hL : 0 < Real.log (1 / x) := by
      rw [one_div, Real.log_inv]
      exact neg_pos.mpr (Real.log_neg hx.1 hx.2)
    exact mul_pos (mul_pos (div_pos (Real.exp_pos _) (by positivity)) (pow_pos hx.1 _)) hL
  · norm_num
theorem gap33 : targetIntegral = seriesApprox 5 + seriesRemainder 5 := by
  exact gap6 5
theorem gap34 :
    seriesApprox 5 + seriesRemainder 5 =
      0.3179 + seriesRemainder 5 + roundingError := by
  unfold roundingError
  ring
theorem gap35 :
    0.3179 + seriesRemainder 5 + roundingError =
      0.3179 + seriesRemainder 5 - |roundingError| := by
  rw [abs_of_neg gap31]
  ring
theorem gap36 :
    0.3179 + seriesRemainder 5 - |roundingError| =
      0.3179 + combinedError := by
  unfold combinedError
  rw [abs_of_neg gap31]
  ring
theorem gap37 : targetIntegral = 0.3179 + combinedError := by
  calc
    targetIntegral = seriesApprox 5 + seriesRemainder 5 := gap33
    _ = 0.3179 + seriesRemainder 5 + roundingError := gap34
    _ = 0.3179 + seriesRemainder 5 - |roundingError| := gap35
    _ = 0.3179 + combinedError := gap36
theorem gap38 :
    |combinedError| =
      |seriesRemainder 5 - abs roundingError| := by
  unfold combinedError
  rw [abs_of_neg gap31]
  ring
theorem gap39 :
    |seriesRemainder 5 - abs roundingError| ≤
      max (seriesRemainder 5) (abs roundingError) := by
  rcases le_total (seriesRemainder 5) (abs roundingError) with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [gap32]
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [abs_nonneg roundingError]
theorem gap40 :
    max (seriesRemainder 5) (abs roundingError) < 10 ^ (-4 : ℤ) := by
  rw [max_lt_iff]
  constructor
  · exact (le_abs_self (seriesRemainder 5)).trans_lt gap21
  · exact gap30.trans_lt (by norm_num)
theorem gap41 :
    |combinedError| < 10 ^ (-4 : ℤ) := by
  rw [gap38]
  exact gap39.trans_lt gap40
theorem gap42 : |targetIntegral - 0.3179| < 10 ^ (-4 : ℤ) := by
  calc
    |targetIntegral - 0.3179| = |combinedError| := by rw [gap37]; congr 1 <;> ring
    _ < 10 ^ (-4 : ℤ) := gap41

theorem gap43 : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
  exact continuous_f.continuousOn
theorem gap44 (x : ℝ) (hx : 0 < x) :
    HasDerivAt f
      (Real.exp x * Real.log x + (Real.exp x - 1) / x) x := by
  have h : HasDerivAt (fun y : ℝ => (Real.exp y - 1) * Real.log y)
      (Real.exp x * Real.log x + (Real.exp x - 1) / x) x := by
    convert ((Real.hasDerivAt_exp x).sub_const 1).mul
      (Real.hasDerivAt_log (ne_of_gt hx)) using 1 <;> ring
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (ne_of_gt hx)] with y hy
  simp [f, hy]
theorem gap45 (x : ℝ) (hx : 0 < x) :
    Real.exp x * Real.log x + (Real.exp x - 1) / x =
      f x + (Real.exp x - 1) / x + Real.log x := by
  rw [f, if_neg (ne_of_gt hx)]
  ring
theorem gap46 (x : ℝ) (hx : 0 < x) :
    HasDerivAt f (f x + (Real.exp x - 1) / x + Real.log x) x := by
  rw [← gap45 x hx]
  exact gap44 x hx
theorem gap47 :
    (∫ x in (0 : ℝ)..1, deriv f x) =
      (∫ x in (0 : ℝ)..1, f x) +
      (∫ x in (0 : ℝ)..1, g x) +
      (∫ x in (0 : ℝ)..1, Real.log x) := by
  have hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1 :=
    continuous_f.intervalIntegrable 0 1
  have hg : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) 1 :=
    continuous_g.intervalIntegrable 0 1
  have hl : IntervalIntegrable Real.log MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_log'
  calc
    (∫ x in (0 : ℝ)..1, deriv f x) =
        ∫ x in (0 : ℝ)..1, (f x + g x) + Real.log x := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      simpa [g, ne_of_gt hx'.1] using (gap46 x hx'.1).deriv
    _ = (∫ x in (0 : ℝ)..1, f x) +
        (∫ x in (0 : ℝ)..1, g x) +
        (∫ x in (0 : ℝ)..1, Real.log x) := by
      rw [intervalIntegral.integral_add (hf.add hg) hl,
        intervalIntegral.integral_add hf hg]
theorem gap48 :
    (∫ x in (0 : ℝ)..1, deriv f x) = f 1 - f 0 := by
  have hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1 :=
    continuous_f.intervalIntegrable 0 1
  have hg : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) 1 :=
    continuous_g.intervalIntegrable 0 1
  have hl : IntervalIntegrable Real.log MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_log'
  have hd : IntervalIntegrable (deriv f) MeasureTheory.volume (0 : ℝ) 1 :=
    ((hf.add hg).add hl).congr fun x hx => by
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      simpa [g, ne_of_gt hx'.1] using (gap46 x hx'.1).deriv.symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) gap43
  · intro x hx
    have h := gap46 x hx.1
    rw [h.deriv]
    exact h
  · exact hd
theorem gap49 : f 1 - f 0 = 0 := by
  simp [f]
theorem gap50 :
    (∫ x in (0 : ℝ)..1, Real.log x) =
      (1 * Real.log 1 - 1) - (0 * Real.log 0 - 0) := by
  rw [integral_log]
  ring
theorem gap51 :
    (1 * Real.log 1 - 1) - (0 * Real.log 0 - 0) = -1 := by
  norm_num
theorem gap52 :
    targetIntegral = (∫ x in (0 : ℝ)..1, g x) - 1 := by
  have htf : targetIntegral = -(∫ x in (0 : ℝ)..1, f x) := by
    unfold targetIntegral
    calc
      (∫ x in (0 : ℝ)..1, (Real.exp x - 1) * Real.log (1 / x)) =
          ∫ x in (0 : ℝ)..1, -f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        by_cases hx0 : x = 0
        · simp [f, hx0]
        · simp only [f, if_neg hx0, one_div, Real.log_inv]
          ring
      _ = -(∫ x in (0 : ℝ)..1, f x) := intervalIntegral.integral_neg
  have hd0 : (∫ x in (0 : ℝ)..1, deriv f x) = 0 := gap48.trans gap49
  have hl : (∫ x in (0 : ℝ)..1, Real.log x) = -1 := gap50.trans gap51
  rw [htf]
  nlinarith [gap47, hd0, hl]
theorem gap53 : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
  exact continuous_g.continuousOn
theorem gap54 (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    nthDeriv n g x =
      (Real.exp x * P n x - (-1 : ℝ) ^ n * n.factorial) / x ^ (n + 1) := by
  let inv : ℝ → ℝ := fun y => y⁻¹
  have heq : g =ᶠ[nhds x] fun y : ℝ => Real.exp y * y⁻¹ - y⁻¹ := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp only [g, if_neg hy, div_eq_mul_inv]
    ring
  have hexp : ContDiffAt ℝ n Real.exp x := Real.contDiff_exp.contDiffAt
  have hinv : ContDiffAt ℝ n inv x := by
    dsimp [inv]
    exact contDiffAt_inv ℝ hx
  have hprod : ContDiffAt ℝ n (fun y : ℝ => Real.exp y * y⁻¹) x :=
    hexp.mul hinv
  have hinv_formula (r : ℕ) :
      iteratedDeriv r inv x = (-1 : ℝ) ^ r * r.factorial / x ^ (r + 1) := by
    dsimp [inv]
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
    rw [show (-1 - (r : ℤ)) = -(r + 1 : ℕ) by omega, zpow_neg]
    simp only [zpow_natCast]
    ring
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) * iteratedDeriv i Real.exp x *
          iteratedDeriv (n - i) inv x) =
        Real.exp x * P n x / x ^ (n + 1) := by
    unfold P
    rw [Finset.mul_sum, Finset.sum_div]
    rw [← Finset.sum_range_reflect
      (fun i => (Nat.choose n i : ℝ) * iteratedDeriv i Real.exp x *
        iteratedDeriv (n - i) inv x) (n + 1)]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n - (n - k) = k := by omega
    rw [Nat.choose_symm hkn, hinv_formula]
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
    rw [hsub]
    have hpows : x ^ (n + 1) = x ^ (n - k) * x ^ (k + 1) := by
      rw [← pow_add]
      congr 1
      omega
    field_simp [pow_ne_zero _ hx]
    rw [hpows]
    ring
  unfold nthDeriv
  rw [← iteratedDeriv_eq_iterate]
  rw [heq.iteratedDeriv_eq n]
  rw [iteratedDeriv_fun_sub hprod hinv]
  rw [iteratedDeriv_fun_mul hexp hinv]
  rw [hsum, hinv_formula]
  ring
theorem gap55 (n : ℕ) (x : ℝ) :
    P n x = ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (-1 : ℝ) ^ k * k.factorial * x ^ (n - k) := by
  rfl
theorem gap56 (n : ℕ) :
    Filter.Tendsto (nthDeriv n g) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (1 / (n + 1 : ℝ))) := by
  rw [nthDeriv_g_eq_expMoment n]
  have h := (expMoment_hasDerivAt n 0).continuousAt
  change Filter.Tendsto (expMoment n) (nhds 0) (nhds (expMoment n 0)) at h
  rw [expMoment_zero n] at h
  exact h.mono_left nhdsWithin_le_nhds
theorem gap57 (n : ℕ) :
    nthDeriv n g 0 = 1 / (n + 1 : ℝ) := by
  rw [nthDeriv_g_eq_expMoment n, expMoment_zero n]
theorem gap58 : fourthDerivG 1 = 9 * Real.exp 1 - 24 := by
  unfold fourthDerivG
  rw [gap54 4 1 one_ne_zero]
  norm_num [P, Finset.sum_range_succ, Nat.factorial, Nat.choose]
  ring
theorem gap59 : 9 * Real.exp 1 - 24 < 0.5 := by
  nlinarith [Real.exp_one_lt_d9]
theorem gap60 : fourthDerivG 1 < 0.5 := by
  rw [gap58]
  exact gap59
theorem gap61 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0.2 ≤ fourthDerivG x := by
  have hfour : fourthDerivG x = expMoment 4 x := by
    exact congrFun (nthDeriv_g_eq_expMoment 4) x
  rw [hfour]
  unfold expMoment
  calc
    (0.2 : ℝ) = ∫ t in (0 : ℝ)..1, t ^ 4 := by
      rw [integral_pow]
      norm_num
    _ ≤ ∫ t in (0 : ℝ)..1, t ^ 4 * Real.exp (t * x) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((by fun_prop : Continuous fun t : ℝ => t ^ 4).intervalIntegrable 0 1)
        ((by fun_prop : Continuous fun t : ℝ => t ^ 4 * Real.exp (t * x)).intervalIntegrable 0 1)
      intro t ht
      have he : 1 ≤ Real.exp (t * x) := by
        nlinarith [Real.add_one_le_exp (t * x), mul_nonneg ht.1 hx.1]
      nlinarith [pow_nonneg ht.1 4]
theorem gap62 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    fourthDerivG x ≤ 0.5 := by
  have hfour : fourthDerivG x = expMoment 4 x := by
    exact congrFun (nthDeriv_g_eq_expMoment 4) x
  rw [hfour]
  unfold expMoment
  let U : ℝ → ℝ := fun t => t ^ 4 * (1 + t * (Real.exp 1 - 1))
  calc
    (∫ t in (0 : ℝ)..1, t ^ 4 * Real.exp (t * x)) ≤ ∫ t in (0 : ℝ)..1, U t := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((by fun_prop : Continuous fun t : ℝ => t ^ 4 * Real.exp (t * x)).intervalIntegrable 0 1)
        ((by dsimp [U]; fun_prop : Continuous U).intervalIntegrable 0 1)
      intro t ht
      have hu0 : 0 ≤ t * x := mul_nonneg ht.1 hx.1
      have hu1 : t * x ≤ 1 := mul_le_one₀ ht.2 hx.1 hx.2
      have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
        (sub_nonneg.mpr hu1) hu0 (by ring : (1 - t * x) + t * x = 1)
      have hchord : Real.exp (t * x) ≤ 1 + (t * x) * (Real.exp 1 - 1) := by
        convert hconv using 1 <;> simp [smul_eq_mul, Real.exp_zero] <;> ring
      have hut : t * x ≤ t := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2 ht.1
      have hexp : Real.exp (t * x) ≤ 1 + t * (Real.exp 1 - 1) := by
        nlinarith [hchord, Real.exp_one_gt_two]
      dsimp [U]
      exact mul_le_mul_of_nonneg_left hexp (pow_nonneg ht.1 4)
    _ = 1 / 5 + (Real.exp 1 - 1) / 6 := by
      calc
        (∫ t in (0 : ℝ)..1, U t) =
            ∫ t in (0 : ℝ)..1, t ^ 4 + (Real.exp 1 - 1) * t ^ 5 := by
          apply intervalIntegral.integral_congr
          intro t ht
          dsimp [U]
          ring
        _ = (∫ t in (0 : ℝ)..1, t ^ 4) +
            ∫ t in (0 : ℝ)..1, (Real.exp 1 - 1) * t ^ 5 := by
          rw [intervalIntegral.integral_add
            ((by fun_prop : Continuous fun t : ℝ => t ^ 4).intervalIntegrable 0 1)
            ((by fun_prop : Continuous fun t : ℝ => (Real.exp 1 - 1) * t ^ 5).intervalIntegrable 0 1)]
        _ = 1 / 5 + (Real.exp 1 - 1) / 6 := by
          rw [intervalIntegral.integral_const_mul, integral_pow, integral_pow]
          norm_num
          ring
    _ ≤ 0.5 := by
      nlinarith [Real.exp_one_lt_d9]
theorem gap63 : (0.2 : ℝ) ≤ 0.5 := by
  norm_num

private theorem targetIntegral_tight :
    (0.3179019 : ℝ) < targetIntegral ∧ targetIntegral < 0.3179024 := by
  have hmain := gap6 10
  have hr := gap9 10
  rw [gap13 11, abs_le] at hr
  unfold seriesApprox at hmain
  simp_rw [gap13] at hmain
  norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at hmain hr ⊢
  constructor <;> nlinarith [Real.exp_one_lt_d9]

private theorem simpsonG_tight :
    (1.3179088 : ℝ) < simpsonG ∧ simpsonG < 1.3179091 := by
  have hq := Real.exp_bound (x := (1 / 4 : ℝ)) (n := 10) (by norm_num) (by norm_num)
  have hh := Real.exp_bound (x := (1 / 2 : ℝ)) (n := 10) (by norm_num) (by norm_num)
  have ht := Real.exp_bound (x := (3 / 4 : ℝ)) (n := 10) (by norm_num) (by norm_num)
  rw [abs_le] at hq hh ht
  norm_num [Finset.sum_range_succ, Nat.factorial] at hq hh ht
  unfold simpsonG g
  norm_num
  constructor <;> nlinarith [hq.1, hq.2, hh.1, hh.2, ht.1, ht.2,
    Real.exp_one_gt_d9, Real.exp_one_lt_d9]

private theorem simpsonRemainderG_tight :
    (-0.0000073 : ℝ) < simpsonRemainderG ∧ simpsonRemainderG < -0.0000063 := by
  have ht := targetIntegral_tight
  have hs := simpsonG_tight
  have hgint : (∫ x in (0 : ℝ)..1, g x) = targetIntegral + 1 := by
    linarith [gap52]
  unfold simpsonRemainderG
  rw [hgint]
  constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2]

theorem gap64 :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      |simpsonRemainderG| =
        |-(fourthDerivG ξ / (180 * 4 ^ 4))| := by
  let c : ℝ := -simpsonRemainderG * (180 * 4 ^ 4)
  have hr := simpsonRemainderG_tight
  have hzero : fourthDerivG 0 = 0.2 := by
    unfold fourthDerivG
    rw [gap57 4]
    norm_num
  have hc0 : fourthDerivG 0 < c := by
    rw [hzero]
    dsimp [c]
    norm_num at hr ⊢
    nlinarith [hr.2]
  have hc1 : c < fourthDerivG 1 := by
    rw [gap58]
    dsimp [c]
    norm_num at hr ⊢
    nlinarith [hr.1, Real.exp_one_gt_d9]
  have hcont : ContinuousOn fourthDerivG (Set.Icc (0 : ℝ) 1) := by
    unfold fourthDerivG
    exact (continuous_nthDeriv_g 4).continuousOn
  have hc_mem : c ∈ Set.Icc (fourthDerivG 0) (fourthDerivG 1) := ⟨hc0.le, hc1.le⟩
  obtain ⟨ξ, hξ, hξeq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hc_mem
  have hξ0 : ξ ≠ 0 := by
    intro h
    subst ξ
    rw [hzero] at hξeq
    nlinarith
  have hξ1 : ξ ≠ 1 := by
    intro h
    subst ξ
    nlinarith [hξeq]
  refine ⟨ξ, ⟨lt_of_le_of_ne hξ.1 (Ne.symm hξ0), lt_of_le_of_ne hξ.2 hξ1⟩, ?_⟩
  rw [hξeq]
  dsimp [c]
  congr 1
  norm_num
  ring
theorem gap65 :
    |simpsonRemainderG| ≤ 1 / (360 * 4 ^ 4) := by
  have hr := simpsonRemainderG_tight
  rw [abs_of_neg (hr.2.trans (by norm_num))]
  norm_num
  linarith [hr.1]
theorem gap66 : simpsonRemainderG < 0 := by
  exact simpsonRemainderG_tight.2.trans (by norm_num)
theorem gap67 :
    |simpsonRemainderG| ≤ 1 / (360 * 4 ^ 4) := by
  exact gap65
theorem gap68 : (1 / (360 * 4 ^ 4) : ℝ) < 1.1 * 10 ^ (-5 : ℤ) := by
  norm_num
theorem gap69 : |simpsonRemainderG| < 1.1 * 10 ^ (-5 : ℤ) := by
  exact gap67.trans_lt gap68
theorem gap70 : g 0 = 1 := by
  simp [g]
theorem gap71 : |g (1 / 4) - 1.13610| < 0.00001 := by
  have h := Real.exp_bound (x := (1 / 4 : ℝ)) (n := 10) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [g, if_neg (by norm_num : (1 / 4 : ℝ) ≠ 0), abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap72 : |g (1 / 2) - 1.29744| < 0.00001 := by
  have h := Real.exp_bound (x := (1 / 2 : ℝ)) (n := 10) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [g, if_neg (by norm_num : (1 / 2 : ℝ) ≠ 0), abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap73 : |g (3 / 4) - 1.48933| < 0.00001 := by
  have h := Real.exp_bound (x := (3 / 4 : ℝ)) (n := 10) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [g, if_neg (by norm_num : (3 / 4 : ℝ) ≠ 0), abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap74 : |g 1 - 1.71828| < 0.00001 := by
  rw [g, if_neg one_ne_zero, abs_lt]
  constructor <;> nlinarith [Real.exp_one_gt_d9, Real.exp_one_lt_d9]
theorem gap75 :
    targetIntegral = (∫ x in (0 : ℝ)..1, g x) - 1 := by
  exact gap52
theorem gap76 :
    |((∫ x in (0 : ℝ)..1, g x) - 1) - (simpsonG - 1)| <
      1.1 * 10 ^ (-5 : ℤ) := by
  simpa [simpsonRemainderG] using gap69
theorem gap77 : |(simpsonG - 1) - (1.3179 - 1)| < 0.0001 := by
  have h71 := gap71
  have h72 := gap72
  have h73 := gap73
  have h74 := gap74
  rw [abs_lt] at h71 h72 h73 h74 ⊢
  unfold simpsonG
  rw [gap70]
  constructor <;> nlinarith [h71.1, h71.2, h72.1, h72.2,
    h73.1, h73.2, h74.1, h74.2]
theorem gap78 : (1.3179 - 1 : ℝ) = 0.3179 := by
  norm_num
theorem gap79 : |targetIntegral - 0.3179| < 0.0001 := by
  convert gap42 using 1 <;> norm_num

end

end ProofGap.Exercise2542
