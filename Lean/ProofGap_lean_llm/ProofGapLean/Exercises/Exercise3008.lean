import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise3008

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def coefficient (n : ℕ) : ℝ := 1 / (4 * (n : ℝ) + 1)

def term (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (4 * n + 1) / (4 * (n : ℝ) + 1)

def seriesFunction (x : ℝ) : ℝ := ∑' n : ℕ, term x n

def convergenceDomain : Set ℝ := {x | Summable (term x)}

def powerSeriesRadius (a : ℕ → ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ x : ℝ, |x| < r → Summable (fun n => a n * x ^ n)}

private theorem ratio_limit :
    Tendsto
      (fun n : ℕ => (4 * (n : ℝ) + 5) / (4 * (n : ℝ) + 1))
      atTop (𝓝 1) := by
  simpa only [add_comm, div_self (by norm_num : (4 : ℝ) ≠ 0)] using
    (tendsto_add_mul_div_add_mul_atTop_nhds
      (5 : ℝ) 1 4 (by norm_num : (4 : ℝ) ≠ 0))

private theorem reverse_ratio_limit :
    Tendsto
      (fun n : ℕ => (4 * (n : ℝ) + 1) / (4 * (n : ℝ) + 5))
      atTop (𝓝 1) := by
  simpa only [add_comm, div_self (by norm_num : (4 : ℝ) ≠ 0)] using
    (tendsto_add_mul_div_add_mul_atTop_nhds
      (1 : ℝ) 5 4 (by norm_num : (4 : ℝ) ≠ 0))

private theorem term_ratio_limit (x : ℝ) (hx : x ≠ 0) :
    Tendsto
      (fun n : ℕ => ‖term x (n + 1)‖ / ‖term x n‖)
      atTop (𝓝 (|x| ^ 4)) := by
  have h :
      Tendsto
        (fun n : ℕ =>
          |x| ^ 4 * ((4 * (n : ℝ) + 1) / (4 * (n : ℝ) + 5)))
        atTop (𝓝 (|x| ^ 4 * 1)) :=
    tendsto_const_nhds.mul reverse_ratio_limit
  convert h using 1
  funext n
  unfold term
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div,
    abs_pow, abs_pow]
  have hxa : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hd1 : |4 * (n : ℝ) + 1| ≠ 0 := by positivity
  have hd5 : |4 * (n : ℝ) + 5| ≠ 0 := by positivity
  rw [abs_of_pos (by positivity : 0 < 4 * (n : ℝ) + 1),
    abs_of_pos (by positivity : 0 < 4 * ((n + 1 : ℕ) : ℝ) + 1)]
  push_cast
  rw [show 4 * ((n : ℝ) + 1) + 1 = 4 * (n : ℝ) + 5 by ring,
    show 4 * (n + 1) + 1 = (4 * n + 1) + 4 by omega,
    pow_add]
  field_simp
  ring

private theorem not_summable_linear_harmonic :
    ¬Summable (fun n : ℕ => 1 / (4 * (n : ℝ) + 1)) := by
  letI : NeZero 4 := ⟨by norm_num⟩
  have h :=
    Real.not_summable_indicator_one_div_natCast
      (m := 4) (by norm_num) (1 : ZMod 4)
  intro hs
  apply h
  apply (summable_indicator_mod_iff_summable
    4 1 (fun n : ℕ => (1 / n : ℝ))).2
  convert hs using 1
  funext n
  norm_num

private theorem not_summable_term_of_abs_eq_one (x : ℝ)
    (hx : |x| = 1) :
    ¬Summable (term x) := by
  intro hs
  apply not_summable_linear_harmonic
  convert hs.norm using 1
  funext n
  unfold term
  rw [Real.norm_eq_abs, abs_div, abs_pow, hx, one_pow,
    abs_of_pos (by positivity : 0 < 4 * (n : ℝ) + 1)]

private theorem summable_term_iff (x : ℝ) :
    Summable (term x) ↔ |x| < 1 := by
  by_cases hx0 : x = 0
  · subst x
    constructor
    · intro
      norm_num
    · intro
      convert (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))) using 1
      funext n
      unfold term
      rw [zero_pow (by omega), zero_div]
  constructor
  · intro hs
    by_contra hlt
    have hge : 1 ≤ |x| := le_of_not_gt hlt
    rcases hge.eq_or_lt with heq | hgt
    · exact not_summable_term_of_abs_eq_one x heq.symm hs
    · exact
        (not_summable_of_ratio_test_tendsto_gt_one
          (one_lt_pow₀ (n := 4) hgt (by norm_num))
          (term_ratio_limit x hx0)) hs
  · intro hlt
    apply summable_of_ratio_test_tendsto_lt_one (f := term x)
      (pow_lt_one₀ (n := 4) (abs_nonneg x) hlt (by norm_num))
    · apply Filter.Eventually.of_forall
      intro n
      unfold term
      exact div_ne_zero (pow_ne_zero (4 * n + 1) hx0) (by positivity)
    · exact term_ratio_limit x hx0

private theorem coefficient_ratio_limit (x : ℝ) (hx : x ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        ‖coefficient (n + 1) * x ^ (n + 1)‖ /
          ‖coefficient n * x ^ n‖)
      atTop (𝓝 |x|) := by
  have h :
      Tendsto
        (fun n : ℕ =>
          |x| * ((4 * (n : ℝ) + 1) / (4 * (n : ℝ) + 5)))
        atTop (𝓝 (|x| * 1)) :=
    tendsto_const_nhds.mul reverse_ratio_limit
  convert h using 1
  funext n
  unfold coefficient
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_div, abs_div, abs_pow, abs_pow]
  rw [abs_of_pos (by positivity : 0 < 4 * (n : ℝ) + 1),
    abs_of_pos (by positivity : 0 < 4 * ((n + 1 : ℕ) : ℝ) + 1)]
  push_cast
  rw [show 4 * ((n : ℝ) + 1) + 1 = 4 * (n : ℝ) + 5 by ring,
    pow_succ]
  have hxa : |x| ≠ 0 := abs_ne_zero.mpr hx
  field_simp
  ring

private theorem not_summable_coefficient_of_abs_eq_one (x : ℝ)
    (hx : |x| = 1) :
    ¬Summable (fun n : ℕ => coefficient n * x ^ n) := by
  intro hs
  apply not_summable_linear_harmonic
  convert hs.norm using 1
  funext n
  unfold coefficient
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_one, abs_pow, hx,
    one_pow, abs_of_pos (by positivity : 0 < 4 * (n : ℝ) + 1)]
  ring

private theorem summable_coefficient_iff (x : ℝ) :
    Summable (fun n : ℕ => coefficient n * x ^ n) ↔ |x| < 1 := by
  by_cases hx0 : x = 0
  · subst x
    constructor
    · intro
      norm_num
    · intro
      apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      rw [zero_pow hn, mul_zero]
  constructor
  · intro hs
    by_contra hlt
    have hge : 1 ≤ |x| := le_of_not_gt hlt
    rcases hge.eq_or_lt with heq | hgt
    · exact not_summable_coefficient_of_abs_eq_one x heq.symm hs
    · exact
        (not_summable_of_ratio_test_tendsto_gt_one
          hgt (coefficient_ratio_limit x hx0)) hs
  · intro hlt
    apply summable_of_ratio_test_tendsto_lt_one
      (f := fun n : ℕ => coefficient n * x ^ n) hlt
    · apply Filter.Eventually.of_forall
      intro n
      unfold coefficient
      exact mul_ne_zero (by positivity) (pow_ne_zero n hx0)
    · exact coefficient_ratio_limit x hx0

private theorem hasDerivAt_term (x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => term y n) (x ^ (4 * n)) x := by
  unfold term
  have h := (hasDerivAt_id x).pow (4 * n + 1)
  convert h.div_const (4 * (n : ℝ) + 1) using 1
  rw [show 4 * n + 1 - 1 = 4 * n by omega]
  push_cast
  have hd : 4 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring
  simp only [id_eq]

private theorem hasDerivAt_seriesFunction (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt seriesFunction (∑' n : ℕ, x ^ (4 * n)) x := by
  have habsx : |x| < 1 := (abs_lt).2 hx
  let r : ℝ := (|x| + 1) / 2
  have hr0 : 0 < r := by
    dsimp [r]
    linarith [abs_nonneg x]
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hxr : |x| < r := by
    dsimp [r]
    linarith
  have hxmem : x ∈ Set.Ioo (-r) r := (abs_lt).1 hxr
  have hu : Summable (fun n : ℕ => (r ^ 4) ^ n) :=
    summable_geometric_of_lt_one (pow_nonneg hr0.le 4)
      (pow_lt_one₀ hr0.le hr1 (by norm_num))
  have hbound :
      ∀ n y, y ∈ Set.Ioo (-r) r →
        ‖y ^ (4 * n)‖ ≤ (r ^ 4) ^ n := by
    intro n y hy
    have hyabs : |y| ≤ r := ((abs_lt).2 hy).le
    rw [Real.norm_eq_abs, abs_pow, ← pow_mul]
    gcongr
  have hsum0 : Summable (fun n : ℕ => term (0 : ℝ) n) :=
    (summable_term_iff 0).2 (by norm_num)
  have h :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
      isPreconnected_Ioo
      (fun n y _ => hasDerivAt_term y n)
      hbound (show (0 : ℝ) ∈ Set.Ioo (-r) r by constructor <;> linarith)
      hsum0 hxmem
  simpa only [seriesFunction] using h

private theorem mem_Ioo_of_mem_uIcc {x t : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (ht : t ∈ Set.uIcc 0 x) :
    t ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [Set.mem_uIcc] at ht
  rcases ht with ht | ht <;> constructor <;> linarith [hx.1, hx.2]

private theorem one_sub_pow_four_ne_zero {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    1 - t ^ 4 ≠ 0 := by
  have habs : |t| < 1 := (abs_lt).2 ht
  have hpabs : |t| ^ 4 < 1 :=
    pow_lt_one₀ (abs_nonneg t) habs (by norm_num)
  have hp : t ^ 4 < 1 := by
    rw [← abs_pow] at hpabs
    exact lt_of_le_of_lt (le_abs_self _) hpabs
  linarith

private theorem integrand_four_continuousOn (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousOn (fun t : ℝ => 1 / (1 - t ^ 4)) (Set.uIcc 0 x) := by
  apply continuousOn_const.div
    (continuousOn_const.sub (continuousOn_id.pow 4))
  intro t ht
  exact one_sub_pow_four_ne_zero (mem_Ioo_of_mem_uIcc hx ht)

private theorem one_sub_pow_two_ne_zero {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    1 - t ^ 2 ≠ 0 := by
  have habs : |t| < 1 := (abs_lt).2 ht
  have hpabs : |t| ^ 2 < 1 :=
    pow_lt_one₀ (abs_nonneg t) habs (by norm_num)
  have hp : t ^ 2 < 1 := by
    rw [← abs_pow] at hpabs
    exact lt_of_le_of_lt (le_abs_self _) hpabs
  linarith

private theorem integrand_minus_continuousOn (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousOn (fun t : ℝ => 1 / (1 - t ^ 2)) (Set.uIcc 0 x) := by
  apply continuousOn_const.div
    (continuousOn_const.sub (continuousOn_id.pow 2))
  intro t ht
  exact one_sub_pow_two_ne_zero (mem_Ioo_of_mem_uIcc hx ht)

private theorem integrand_plus_continuousOn (x : ℝ) :
    ContinuousOn (fun t : ℝ => 1 / (1 + t ^ 2)) (Set.uIcc 0 x) := by
  apply continuousOn_const.div
    (continuousOn_const.add (continuousOn_id.pow 2))
  intro t ht
  change (1 : ℝ) + t ^ 2 ≠ 0
  nlinarith [sq_nonneg t]

private theorem hasDerivAt_logPrimitive (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (fun y : ℝ =>
        (1 / 2 : ℝ) *
          (Real.log (1 + y) - Real.log (1 - y)))
      (1 / (1 - t ^ 2)) t := by
  have hplus : 1 + t ≠ 0 := by linarith [ht.1]
  have hminus : 1 - t ≠ 0 := by linarith [ht.2]
  have hp :
      HasDerivAt (fun y : ℝ => Real.log (1 + y))
        (1 / (1 + t)) t := by
    simpa [one_div] using
      (((hasDerivAt_const t 1).add (hasDerivAt_id t)).log hplus)
  have hm :
      HasDerivAt (fun y : ℝ => Real.log (1 - y))
        (-1 / (1 - t)) t := by
    simpa [one_div] using
      (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).log hminus)
  convert (hasDerivAt_const t (1 / 2 : ℝ)).mul (hp.sub hm) using 1
  have hsq := one_sub_pow_two_ne_zero ht
  field_simp [hplus, hminus, hsq]
  ring

private theorem integral_one_div_one_sub_sq (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t in 0..x, 1 / (1 - t ^ 2)) =
      (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) := by
  have hderiv :
      ∀ t ∈ Set.uIcc 0 x,
        HasDerivAt
          (fun y : ℝ =>
            (1 / 2 : ℝ) *
              (Real.log (1 + y) - Real.log (1 - y)))
          (1 / (1 - t ^ 2)) t := by
    intro t ht
    exact hasDerivAt_logPrimitive t (mem_Ioo_of_mem_uIcc hx ht)
  have hft :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (integrand_minus_continuousOn x hx).intervalIntegrable
  have hplus : 1 + x ≠ 0 := by linarith [hx.1]
  have hminus : 1 - x ≠ 0 := by linarith [hx.2]
  rw [Real.log_div hplus hminus]
  simpa using hft

theorem gap1 :
    ∃ a : ℕ → ℝ,
      (∀ n, a n = coefficient n) ∧
      Tendsto (fun n : ℕ => |a n / a (n + 1)|) atTop (𝓝 1) ∧
      Tendsto
        (fun n : ℕ => (4 * (n : ℝ) + 5) / (4 * (n : ℝ) + 1))
        atTop (𝓝 1) := by
  refine ⟨coefficient, fun n => rfl, ?_, ratio_limit⟩
  convert ratio_limit using 1
  funext n
  unfold coefficient
  have h1 : (4 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h5 : (4 * (n : ℝ) + 5) ≠ 0 := by positivity
  rw [abs_of_pos (div_pos (by positivity) (by positivity))]
  push_cast
  field_simp
  ring

theorem gap2 :
    Tendsto
      (fun n : ℕ => (4 * (n : ℝ) + 5) / (4 * (n : ℝ) + 1))
      atTop (𝓝 1) := by
  exact ratio_limit

theorem gap3 :
    ∃ a : ℕ → ℝ,
      (∀ n, a n = coefficient n) ∧
      Tendsto (fun n : ℕ => |a n / a (n + 1)|) atTop (𝓝 1) := by
  obtain ⟨a, ha, hlim, _⟩ := gap1
  exact ⟨a, ha, hlim⟩

theorem gap4 : powerSeriesRadius coefficient = 1 := by
  have hset :
      {r : ℝ | 0 ≤ r ∧
        ∀ x : ℝ, |x| < r →
          Summable (fun n => coefficient n * x ^ n)} =
        Set.Icc (0 : ℝ) 1 := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hr0, hr⟩
      refine ⟨hr0, ?_⟩
      by_contra hle
      have hr1 : 1 < r := lt_of_not_ge hle
      let x : ℝ := (r + 1) / 2
      have hxpos : 0 < x := by dsimp [x]; linarith
      have hxr : |x| < r := by
        rw [abs_of_pos hxpos]
        dsimp [x]
        linarith
      have hx1 := (summable_coefficient_iff x).mp (hr x hxr)
      rw [abs_of_pos hxpos] at hx1
      dsimp [x] at hx1
      linarith
    · rintro ⟨hr0, hr1⟩
      refine ⟨hr0, ?_⟩
      intro x hx
      exact (summable_coefficient_iff x).mpr (lt_of_lt_of_le hx hr1)
  unfold powerSeriesRadius
  rw [hset]
  norm_num

theorem gap5 (x : ℝ) (hx : |x| = 1) :
    ¬Summable (term x) := by
  exact not_summable_term_of_abs_eq_one x hx

theorem gap6 : convergenceDomain = Set.Ioo (-1) 1 := by
  ext x
  simp only [convergenceDomain, Set.mem_setOf_eq, Set.mem_Ioo]
  rw [summable_term_iff, abs_lt]

theorem gap7 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv seriesFunction x = ∑' n : ℕ, x ^ (4 * n) := by
  exact (hasDerivAt_seriesFunction x hx).deriv

theorem gap8 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∑' n : ℕ, x ^ (4 * n)) = 1 / (1 - x ^ 4) := by
  have habs : |x| < 1 := (abs_lt).2 hx
  have hpow : |x ^ 4| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg x) habs (by norm_num)
  have hfun :
      (fun n : ℕ => x ^ (4 * n)) = fun n : ℕ => (x ^ 4) ^ n := by
    funext n
    rw [pow_mul]
  rw [hfun]
  simpa only [one_div] using tsum_geometric_of_abs_lt_one hpow

theorem gap9 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv seriesFunction x = 1 / (1 - x ^ 4) := by
  rw [gap7 x hx, gap8 x hx]

theorem gap10 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    seriesFunction 0 = 0 := by
  unfold seriesFunction
  have hz : term (0 : ℝ) = fun _ : ℕ => (0 : ℝ) := by
    funext n
    unfold term
    rw [zero_pow (by omega), zero_div]
  rw [hz]
  simp

theorem gap11 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    seriesFunction x = ∫ t in 0..x, deriv seriesFunction t := by
  have hdiff :
      ∀ t ∈ Set.uIcc 0 x, DifferentiableAt ℝ seriesFunction t := by
    intro t ht
    exact (hasDerivAt_seriesFunction t
      (mem_Ioo_of_mem_uIcc hx ht)).differentiableAt
  have heq :
      Set.EqOn (deriv seriesFunction)
        (fun t : ℝ => 1 / (1 - t ^ 4)) (Set.uIcc 0 x) := by
    intro t ht
    exact gap9 t (mem_Ioo_of_mem_uIcc hx ht)
  have hint :
      IntervalIntegrable (deriv seriesFunction)
        MeasureTheory.volume 0 x := by
    rw [intervalIntegrable_congr (heq.mono Set.uIoc_subset_uIcc)]
    exact (integrand_four_continuousOn x hx).intervalIntegrable
  have hft :=
    intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [hft, gap10 x hx]
  ring

theorem gap12 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t in 0..x, deriv seriesFunction t) =
      ∫ t in 0..x, 1 / (1 - t ^ 4) := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact gap9 t (mem_Ioo_of_mem_uIcc hx ht)

theorem gap13 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t in 0..x, 1 / (1 - t ^ 4)) =
      (1 / 2 : ℝ) * (∫ t in 0..x, 1 / (1 - t ^ 2)) +
      (1 / 2 : ℝ) * (∫ t in 0..x, 1 / (1 + t ^ 2)) := by
  let f : ℝ → ℝ := fun t => 1 / (1 - t ^ 2)
  let g : ℝ → ℝ := fun t => 1 / (1 + t ^ 2)
  have hf : IntervalIntegrable f MeasureTheory.volume 0 x := by
    exact (integrand_minus_continuousOn x hx).intervalIntegrable
  have hg : IntervalIntegrable g MeasureTheory.volume 0 x := by
    exact (integrand_plus_continuousOn x).intervalIntegrable
  change
    (∫ t in 0..x, 1 / (1 - t ^ 4)) =
      (1 / 2 : ℝ) * (∫ t in 0..x, f t) +
        (1 / 2 : ℝ) * (∫ t in 0..x, g t)
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hf.const_mul (1 / 2))
      (hg.const_mul (1 / 2))]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' := mem_Ioo_of_mem_uIcc hx ht
  have hm := one_sub_pow_two_ne_zero ht'
  have h4 := one_sub_pow_four_ne_zero ht'
  have hp : 1 + t ^ 2 ≠ 0 := by positivity
  dsimp [f, g]
  field_simp [hm, hp, h4]
  ring

theorem gap14 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 / 2 : ℝ) * (∫ t in 0..x, 1 / (1 - t ^ 2)) +
        (1 / 2 : ℝ) * (∫ t in 0..x, 1 / (1 + t ^ 2)) =
      (1 / 4 : ℝ) * Real.log ((1 + x) / (1 - x)) +
        (1 / 2 : ℝ) * Real.arctan x := by
  rw [integral_one_div_one_sub_sq x hx,
    integral_one_div_one_add_sq]
  norm_num
  ring

theorem gap15 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    seriesFunction x =
      (1 / 4 : ℝ) * Real.log ((1 + x) / (1 - x)) +
        (1 / 2 : ℝ) * Real.arctan x := by
  rw [gap11 x hx, gap12 x hx, gap13 x hx, gap14 x hx]

end

end ProofGap.Exercise3008
