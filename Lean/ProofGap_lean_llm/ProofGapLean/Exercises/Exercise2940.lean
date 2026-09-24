import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter

namespace ProofGap.Exercise2940

noncomputable section

open scoped BigOperators Interval

def f (x : ℝ) : ℝ :=
  x

def a (_n : ℕ) : ℝ :=
  0

def b (n : ℕ) : ℝ :=
  if n = 0 then 0
  else (-1 : ℝ) ^ (n - 1) * (2 / (n : ℝ))

def sawtoothSeries (x : ℝ) : ℝ :=
  2 * ∑'[SummationFilter.conditional ℕ] k : ℕ,
    (-1 : ℝ) ^ k *
      (Real.sin (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))

private def baseTerm (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * Real.sin (((k + 1 : ℕ) : ℝ) * x) /
    ((k + 1 : ℕ) : ℝ)

private theorem seriesHasSum_of_tendsto {u : ℕ → ℝ} {a : ℝ}
    (h : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, u n) atTop (nhds a)) :
    ProofGap.SeriesHasSum u a := by
  change Tendsto (fun s : Finset ℕ ↦ ∑ n ∈ s, u n)
    (SummationFilter.conditional ℕ).filter (nhds a)
  rw [SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
  simpa [Function.comp_def] using h

private theorem hasSum_log_one_add_shifted {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum
      (fun n : ℕ ↦
        (-1 : ℂ) ^ n * z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      (Complex.log (1 + z)) := by
  simpa [pow_succ] using
    (hasSum_nat_add_iff' 1).2 (Complex.hasSum_taylorSeries_log hz)

private theorem seriesHasSum_baseTerm
    (x : ℝ) (hxneg : -Real.pi < x) (hxpos : x < Real.pi) :
    ProofGap.SeriesHasSum (baseTerm x) (x / 2) := by
  let z : ℂ := Complex.exp ((x : ℂ) * Complex.I)
  let q : ℂ := -z
  have hzNorm : ‖z‖ = 1 := by
    simp [z, Complex.norm_exp]
  have hhalf : x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcos : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo hhalf
  have hcosDouble :
      Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    nth_rw 1 [show x = 2 * (x / 2) by ring]
    exact Real.cos_two_mul (x / 2)
  have hsinDouble :
      Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    nth_rw 1 [show x = 2 * (x / 2) by ring]
    exact Real.sin_two_mul (x / 2)
  have hfactor :
      (1 : ℂ) + z =
        ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
          Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) := by
    dsimp [z]
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, zero_mul, add_zero, mul_one]
      rw [hcosDouble]
      ring
    · simp only [Complex.add_im, Complex.one_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, zero_mul, add_zero, mul_one, zero_add]
      rw [hsinDouble]
      ring
  have hone : (1 : ℂ) + z ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hcos.ne'))
      (Complex.exp_ne_zero _)
  have hq : q ≠ 1 := by
    intro h
    apply hone
    calc
      (1 : ℂ) + z = 1 - q := by simp [q]
      _ = 0 := by rw [h]; ring
  have hqNorm : ‖q‖ = 1 := by simp [q, hzNorm]
  have hden : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
  have hgeom :
      ∀ N : ℕ,
        ‖∑ n ∈ Finset.range N, q ^ n‖ ≤ 2 / ‖q - 1‖ := by
    intro N
    rw [geom_sum_eq hq, norm_div]
    apply (div_le_div_iff_of_pos_right hden).2
    calc
      ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hqNorm]; norm_num
  have hanti : Antitone (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) := by
    exact antitone_iff_forall_lt.mpr fun _ _ _ ↦ by gcongr
  have hzero :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [one_div] using
      (Filter.tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hcauchy :
      CauchySeq
        (fun N ↦ ∑ n ∈ Finset.range N,
          ((1 : ℝ) / ((n : ℝ) + 1)) • (z * q ^ n)) := by
    apply hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero
    intro N
    rw [← Finset.mul_sum, norm_mul, hzNorm, one_mul]
    exact hgeom N
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hphaseAlg :
      ∀ n : ℕ, (-1 : ℂ) ^ n * z ^ (n + 1) = z * q ^ n := by
    intro n
    rw [show q = -z by rfl, neg_pow, pow_succ]
    ring
  have hzPow :
      ∀ n : ℕ,
        z ^ (n + 1) =
          Complex.exp
            (((((n + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
    intro n
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hphaseIm :
      ∀ n : ℕ,
        (z * q ^ n).im =
          (-1 : ℝ) ^ n * Real.sin (((n + 1 : ℕ) : ℝ) * x) := by
    intro n
    rw [← hphaseAlg n, hzPow n, Complex.exp_ofReal_mul_I]
    have hnegCast :
        (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
      norm_cast
    rw [hnegCast]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, add_zero, mul_zero, mul_one, zero_add]
  have himTerm :
      ∀ n : ℕ,
        (((1 : ℝ) / ((n : ℝ) + 1)) • (z * q ^ n)).im =
          baseTerm x n := by
    intro n
    rw [Complex.smul_im, hphaseIm n]
    simp [baseTerm, Nat.cast_add, div_eq_mul_inv]
    ring
  have hbase :
      Tendsto (fun N ↦ ∑ n ∈ Finset.range N, baseTerm x n)
        atTop (nhds l.im) := by
    have him := (Complex.continuous_im.tendsto l).comp hl
    have hfun :
        (fun N ↦ ∑ n ∈ Finset.range N, baseTerm x n) =
          Complex.im ∘
            (fun N ↦ ∑ n ∈ Finset.range N,
              ((1 : ℝ) / ((n : ℝ) + 1)) • (z * q ^ n)) := by
      funext N
      rw [Function.comp_apply, Complex.im_sum]
      exact Finset.sum_congr rfl (fun n _ ↦ (himTerm n).symm)
    rw [hfun]
    exact him
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hbase
  have hmono : nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds 1 :=
    tendsto_nhdsWithin_of_tendsto_nhds fun _ a ↦ a
  replace hab := hab.mul hmono
  rw [mul_one] at hab
  replace hab :
      Tendsto
        (fun r : ℝ ↦
          (Complex.log (1 + (r : ℂ) * z)).im)
        (nhdsWithin 1 (Set.Iio 1)) (nhds l.im) := by
    apply hab.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 1, zero_lt_one
    intro r hr1 hr2
    rw [Real.dist_eq, abs_sub_lt_iff] at hr1
    rw [Set.mem_Iio] at hr2
    have hr : |r| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have hrNorm : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, hzNorm, mul_one]
      exact hr
    have hs := Complex.hasSum_im (hasSum_log_one_add_shifted hrNorm)
    rw [← hs.tsum_eq, ← tsum_mul_right]
    apply tsum_congr
    intro n
    have heq :
        (-1 : ℂ) ^ n * ((r : ℂ) * z) ^ (n + 1) /
            ((n + 1 : ℕ) : ℂ) =
          (r ^ n * r) •
            (((1 : ℝ) / ((n : ℝ) + 1)) • (z * q ^ n)) := by
      calc
        (-1 : ℂ) ^ n * ((r : ℂ) * z) ^ (n + 1) /
              ((n + 1 : ℕ) : ℂ) =
            ((r : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) *
              ((-1 : ℂ) ^ n * z ^ (n + 1)) := by
          rw [mul_pow]
          ring
        _ = ((r : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) *
              (z * q ^ n) := by rw [hphaseAlg n]
        _ = (r ^ n * r) •
              (((1 : ℝ) / ((n : ℝ) + 1)) • (z * q ^ n)) := by
          push_cast
          simp [smul_smul, pow_succ, Nat.cast_add, div_eq_mul_inv]
          ring
    rw [heq, Complex.smul_im, himTerm n]
    simp only [smul_eq_mul]
    ring
  have harg : Complex.arg ((1 : ℂ) + z) = x / 2 := by
    rw [hfactor, Complex.arg_real_mul _ (mul_pos (by norm_num) hcos),
      Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hslit : (1 : ℂ) + z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff_arg.mpr
    exact ⟨by rw [harg]; nlinarith [Real.pi_pos], hone⟩
  have hlogIm : (Complex.log ((1 : ℂ) + z)).im = x / 2 := by
    rw [Complex.log_im, harg]
  have hcont :
      ContinuousAt
        (fun r : ℝ ↦ (Complex.log (1 + (r : ℂ) * z)).im) 1 := by
    apply Complex.continuous_im.continuousAt.comp
    apply (show ContinuousAt (fun r : ℝ ↦ (1 : ℂ) + (r : ℂ) * z) 1 by
      fun_prop).clog
    simpa using hslit
  have hcont' :
      Tendsto
        (fun r : ℝ ↦ (Complex.log (1 + (r : ℂ) * z)).im)
        (nhdsWithin 1 (Set.Iio 1)) (nhds (x / 2)) := by
    convert hcont.tendsto.mono_left hmono using 1
    simpa using hlogIm.symm
  have hlIm : l.im = x / 2 := tendsto_nhds_unique hab hcont'
  rw [hlIm] at hbase
  exact seriesHasSum_of_tendsto hbase

private theorem sawtoothSeries_eq_self
    (x : ℝ) (hxneg : -Real.pi < x) (hxpos : x < Real.pi) :
    sawtoothSeries x = x := by
  have hbase := seriesHasSum_baseTerm x hxneg hxpos
  rw [sawtoothSeries]
  have hterms :
      (∑'[SummationFilter.conditional ℕ] k : ℕ,
        (-1 : ℝ) ^ k *
          (Real.sin (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))) =
        ∑'[SummationFilter.conditional ℕ] k : ℕ, baseTerm x k := by
    apply tsum_congr
    intro k
    simp [baseTerm]
    ring
  rw [hterms, hbase.tsum_eq]
  ring

private def mulSinAntiderivative (c x : ℝ) : ℝ :=
  -(x * Real.cos (c * x)) / c + Real.sin (c * x) / c ^ 2

private theorem hasDerivAt_mulSinAntiderivative
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (mulSinAntiderivative c) (x * Real.sin (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (c * y))
        (-Real.sin (c * x) * c) x :=
    (Real.hasDerivAt_cos (c * x)).comp x hinner
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (c * y))
        (Real.cos (c * x) * c) x :=
    (Real.hasDerivAt_sin (c * x)).comp x hinner
  convert
    ((((hasDerivAt_id x).mul hcos).neg).div_const c).add
      (hsin.div_const (c ^ 2)) using 1
  field_simp [hc]
  simp only [id_eq]
  ring

private theorem integral_mul_sin_eq_sub
    (c : ℝ) (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, x * Real.sin (c * x)) =
      mulSinAntiderivative c v - mulSinAntiderivative c u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_mulSinAntiderivative c hc x)
    ((continuous_id.mul
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable u v)

private theorem neg_one_pow_nat_eq_neg_pred
    (n : ℕ) (hn : 0 < n) :
    (-1 : ℝ) ^ n = -(-1 : ℝ) ^ (n - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]
  simp [pow_succ]

private theorem integral_zero_pi_mul_sin_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, x * Real.sin ((n : ℝ) * x)) =
      (-1 : ℝ) ^ (n - 1) * (Real.pi / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [integral_mul_sin_eq_sub (n : ℝ) hn0]
  simp [mulSinAntiderivative, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi, neg_one_pow_nat_eq_neg_pred n hn]
  ring

private theorem integral_neg_pi_pi_mul_sin_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (-Real.pi)..Real.pi,
      x * Real.sin ((n : ℝ) * x)) =
      2 * (-1 : ℝ) ^ (n - 1) * (Real.pi / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [integral_mul_sin_eq_sub (n : ℝ) hn0]
  simp [mulSinAntiderivative, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi, neg_one_pow_nat_eq_neg_pred n hn]
  ring

theorem gap1 :
    Function.Odd f := by
  intro x
  simp [f]

theorem gap2 :
    ∀ n : ℕ, a 0 = a n := by
  simp [a]

theorem gap3 :
    ∀ n : ℕ, a n = 0 := by
  simp [a]

theorem gap4 :
    a 0 = 0 := by
  simp [a]

theorem gap5 :
    ∀ n : ℕ,
      b n =
        1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
          x * Real.sin ((n : ℝ) * x) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [b]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [integral_neg_pi_pi_mul_sin_nat n hnpos]
    simp [b, hn]
    field_simp [Real.pi_ne_zero, Nat.cast_ne_zero.mpr hn]

theorem gap6 :
    ∀ n : ℕ,
      (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
        x * Real.sin ((n : ℝ) * x)) =
        2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
          x * Real.sin ((n : ℝ) * x) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [integral_neg_pi_pi_mul_sin_nat n hnpos,
      integral_zero_pi_mul_sin_nat n hnpos]
    ring

theorem gap7 :
    ∀ n : ℕ, 0 < n →
      (2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
        x * Real.sin ((n : ℝ) * x)) =
        (-1 : ℝ) ^ (n - 1) * (2 / (n : ℝ)) := by
  intro n hn
  rw [integral_zero_pi_mul_sin_nat n hn]
  field_simp [Real.pi_ne_zero, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]

theorem gap8 :
    ∀ n : ℕ, 0 < n →
      b n = (-1 : ℝ) ^ (n - 1) * (2 / (n : ℝ)) := by
  intro n hn
  simp [b, Nat.ne_of_gt hn]

theorem gap9 :
    ∀ x : ℝ, -Real.pi < x → x < Real.pi →
      f x = sawtoothSeries x := by
  intro x hxneg hxpos
  rw [f, sawtoothSeries_eq_self x hxneg hxpos]

theorem gap10 :
    ∀ x : ℝ, -Real.pi < x → x < Real.pi →
      sawtoothSeries x = x := by
  exact sawtoothSeries_eq_self

theorem gap11 :
    ∀ x : ℝ, f x = x := by
  simp [f]

end

end ProofGap.Exercise2940
