import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2946

noncomputable section

open scoped Interval

def Nonintegral (a : ℝ) : Prop :=
  ∀ z : ℤ, a ≠ (z : ℝ)

def coefficientIntegral (a : ℝ) (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi,
      Real.sin (a * x) * Real.sin ((n : ℝ) * x)

def productToSumIntegral (a : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in 0..Real.pi,
      (Real.cos (((n : ℝ) - a) * x) -
        Real.cos (((n : ℝ) + a) * x))

def fourierSeries (a x : ℝ) : ℝ :=
  2 * Real.sin (a * Real.pi) / Real.pi *
    ∑' k : ℕ,
      ((-1 : ℝ) ^ (k + 2) * (k + 1 : ℝ) *
        Real.sin ((k + 1 : ℝ) * x)) /
        ((k + 1 : ℝ) ^ 2 - a ^ 2)

private lemma one_add_exp_mul_I (x : ℝ) :
    (1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I) =
      ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
        Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, sub_zero, zero_mul]
    rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
    ring_nf
  · simp only [Complex.add_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, zero_mul, zero_add]
    rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]
    ring_nf

private lemma one_add_exp_mul_I_ne_zero {x : ℝ}
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    (1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := by
  rw [one_add_exp_mul_I]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (by
      have := Real.cos_pos_of_mem_Ioo (x := x / 2) ⟨by linarith, by linarith⟩
      positivity))
    (Complex.exp_ne_zero _)

private lemma log_one_add_exp_mul_I_im {x : ℝ}
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    (Complex.log ((1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I))).im = x / 2 := by
  have hcos : 0 < 2 * Real.cos (x / 2) := by
    have := Real.cos_pos_of_mem_Ioo (x := x / 2) ⟨by linarith, by linarith⟩
    positivity
  rw [one_add_exp_mul_I,
    Complex.log_ofReal_mul hcos (Complex.exp_ne_zero _), Complex.add_im,
    Complex.ofReal_im, zero_add, Complex.log_exp]
  · simp
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, sub_zero]
    norm_num
    linarith [Real.pi_pos]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, sub_zero]
    norm_num
    linarith [Real.pi_pos]

private lemma complex_sawtooth_limit {x : ℝ}
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        (1 / (k + 1 : ℝ)) •
          (-(-Complex.exp ((x : ℂ) * Complex.I)) ^ (k + 1)))
      Filter.atTop
      (nhds (Complex.log ((1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I)))) := by
  let e : ℂ := Complex.exp ((x : ℂ) * Complex.I)
  let q : ℂ := -e
  let c : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  let z : ℕ → ℂ := fun k => -(q ^ (k + 1))
  have he_norm : ‖e‖ = 1 := by
    simpa [e] using Complex.norm_exp_ofReal_mul_I x
  have hq_norm : ‖q‖ = 1 := by simp [q, he_norm]
  have hq : q ≠ 1 := by
    intro h
    apply one_add_exp_mul_I_ne_zero hx₀ hx₁
    calc
      (1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I) = 1 - q := by simp [q, e]
      _ = 0 := by rw [h]; ring
  have hc_anti : Antitone c := by
    intro m n hmn
    dsimp [c]
    gcongr
  have hc_zero : Filter.Tendsto c Filter.atTop (nhds 0) := by
    simpa [c] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hz_bound : ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N, z k‖ ≤ 2 / ‖q - 1‖ := by
    intro N
    have hsum :
        (∑ k ∈ Finset.range N, z k) =
          -(∑ k ∈ Finset.range N, q ^ k) * q := by
      simp only [z, pow_succ]
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
      ring
    rw [hsum, geom_sum_eq hq, norm_mul, norm_neg, hq_norm,
      mul_one, norm_div]
    gcongr
    calc
      ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hq_norm]; norm_num
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete
    (hc_anti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      hc_zero hz_bound)
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  rw [Filter.tendsto_map'_iff] at habel
  change Filter.Tendsto
    (fun r : ℝ => ∑' k : ℕ, (c k • z k) * (r : ℂ) ^ k)
    (nhdsWithin 1 (Set.Iio 1)) (nhds l) at habel
  have hslit : (1 : ℂ) + e ∈ Complex.slitPlane := by
    rw [show (1 : ℂ) + e =
      ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
        Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) by
          simpa [e] using one_add_exp_mul_I x]
    rw [Complex.mem_slitPlane_iff]
    left
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.exp_ofReal_mul_I_re]
    have hcpos := Real.cos_pos_of_mem_Ioo (x := x / 2)
      ⟨by linarith, by linarith⟩
    positivity
  have hlimit : Filter.Tendsto
      (fun r : ℝ =>
        Complex.log ((1 : ℂ) + (r : ℂ) * e) / (r : ℂ))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (Complex.log ((1 : ℂ) + e))) := by
    have harg : ContinuousAt
        (fun r : ℝ => (1 : ℂ) + (r : ℂ) * e) 1 := by fun_prop
    have hlog := (harg.clog (by simpa using hslit)).tendsto
    have hcoe : ContinuousAt (fun r : ℝ => (r : ℂ)) 1 := by fun_prop
    have hdiv := hlog.div hcoe.tendsto (by norm_num)
    simpa using hdiv.mono_left inf_le_left
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1),
      (∑' k : ℕ, (c k • z k) * (r : ℂ) ^ k) =
        Complex.log ((1 : ℂ) + (r : ℂ) * e) / (r : ℂ) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hrnorm : ‖(r : ℂ) * e‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, he_norm,
        mul_one, abs_of_pos hr.1]
      exact hr.2
    have htaylor := Complex.hasSum_taylorSeries_log hrnorm
    have htail := (hasSum_nat_add_iff' 1).mpr htaylor
    simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, sub_zero] at htail
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.1.ne'
    have hscaled := htail.div_const (r : ℂ)
    calc
      (∑' k : ℕ, (c k • z k) * (r : ℂ) ^ k) =
          ∑' k : ℕ,
            (-1 : ℂ) ^ (k + 1 + 1) * ((r : ℂ) * e) ^ (k + 1) /
              (k + 1 : ℕ) / (r : ℂ) := by
        apply tsum_congr
        intro k
        dsimp [c, z, q]
        have hkR : (k : ℝ) + 1 ≠ 0 := by positivity
        have hkC : (k : ℂ) + 1 ≠ 0 := by
          intro h
          have hre := congrArg Complex.re h
          simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
            Complex.zero_re] at hre
          have : 0 < (k : ℝ) + 1 := by positivity
          linarith
        simp only [one_div, Complex.ofReal_inv, Nat.cast_add, Nat.cast_one]
        field_simp [hkR, hkC, hr0]
        rw [mul_pow]
        push_cast
        ring_nf
      _ = Complex.log ((1 : ℂ) + (r : ℂ) * e) / (r : ℂ) := hscaled.tsum_eq
  have habel' := habel.congr' heq
  exact (tendsto_nhds_unique habel' hlimit) ▸ hl

private lemma complex_sawtooth_term_im (x : ℝ) (k : ℕ) :
    (((1 / (k + 1 : ℝ)) •
      (-(-Complex.exp ((x : ℂ) * Complex.I)) ^ (k + 1)) : ℂ)).im =
      (-1 : ℝ) ^ (k + 2) * Real.sin ((k + 1 : ℝ) * x) /
        (k + 1 : ℝ) := by
  let e : ℂ := Complex.exp ((x : ℂ) * Complex.I)
  have hepow : (e ^ (k + 1)).im = Real.sin ((k + 1 : ℝ) * x) := by
    rw [← Complex.exp_nat_mul]
    have harg : (((k + 1 : ℕ) : ℂ)) * ((x : ℂ) * Complex.I) =
        ((((k + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_im]
    norm_num
  have hz : -(-e) ^ (k + 1) =
      (-1 : ℂ) ^ (k + 2) * e ^ (k + 1) := by
    rw [show -e = (-1 : ℂ) * e by ring, mul_pow,
      show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  rw [show Complex.exp ((x : ℂ) * Complex.I) = e by rfl, hz]
  have hsignRe : ((-1 : ℂ) ^ (k + 2)).re = (-1 : ℝ) ^ (k + 2) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  have hsignIm : ((-1 : ℂ) ^ (k + 2)).im = 0 := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_pow, Complex.ofReal_im]
  rw [Complex.smul_im, Complex.mul_im, hsignRe, hsignIm, hepow]
  simp only [zero_mul, add_zero, smul_eq_mul]
  ring

private lemma sawtooth_series_hasSum {x : ℝ}
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    ProofGap.SeriesHasSum
      (fun k : ℕ =>
        (-1 : ℝ) ^ (k + 2) * Real.sin ((k + 1 : ℝ) * x) /
          (k + 1 : ℝ))
      (x / 2) := by
  have hcomplex := complex_sawtooth_limit hx₀ hx₁
  have him := (Complex.imCLM.continuous.tendsto _).comp hcomplex
  change Filter.Tendsto
    (fun N : ℕ =>
      (∑ k ∈ Finset.range N,
        (1 / (k + 1 : ℝ)) •
          (-(-Complex.exp ((x : ℂ) * Complex.I)) ^ (k + 1))).im)
    Filter.atTop
    (nhds (Complex.log ((1 : ℂ) +
      Complex.exp ((x : ℂ) * Complex.I))).im) at him
  rw [log_one_add_exp_mul_I_im hx₀ hx₁] at him
  unfold ProofGap.SeriesHasSum HasSum
  rw [SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  change Filter.Tendsto
    (fun N : ℕ => ∑ k ∈ Finset.range N,
      (-1 : ℝ) ^ (k + 2) * Real.sin ((k + 1 : ℝ) * x) /
        (k + 1 : ℝ))
    Filter.atTop (nhds (x / 2))
  apply him.congr'
  filter_upwards with N
  change Complex.imCLM
      (∑ k ∈ Finset.range N,
        (1 / (k + 1 : ℝ)) •
          (-(-Complex.exp ((x : ℂ) * Complex.I)) ^ (k + 1))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact complex_sawtooth_term_im x k

private def remainderScalar (a : ℝ) : ℝ :=
  Real.sin (a * Real.pi) / Real.pi

private def periodicRemainder (a t : ℝ) : ℂ :=
  (Real.sin (a * t) - remainderScalar a * t : ℝ)

private def periodicRemainder' (a t : ℝ) : ℂ :=
  (a * Real.cos (a * t) - remainderScalar a : ℝ)

private def periodicRemainder'' (a t : ℝ) : ℂ :=
  (-a ^ 2 * Real.sin (a * t) : ℝ)

private lemma periodicRemainder_endpoints (a : ℝ) :
    periodicRemainder a (-Real.pi) = periodicRemainder a Real.pi := by
  unfold periodicRemainder remainderScalar
  rw [mul_neg, Real.sin_neg]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

private noncomputable def remainderCircle (a : ℝ) :
    C(AddCircle (2 * Real.pi), ℂ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact
    { toFun := AddCircle.liftIoc (2 * Real.pi) (-Real.pi)
        (periodicRemainder a)
      continuous_toFun := by
        apply AddCircle.liftIoc_continuous
        · convert periodicRemainder_endpoints a using 1 <;> ring
        · unfold periodicRemainder
          fun_prop }

private lemma hasDerivAt_periodicRemainder (a t : ℝ) :
    HasDerivAt (periodicRemainder a) (periodicRemainder' a t) t := by
  have hinner : HasDerivAt (fun y : ℝ => a * y) a t := by
    convert (hasDerivAt_id t).const_mul a using 1 <;> ring
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (a * y))
      (a * Real.cos (a * t)) t := by
    convert Real.hasDerivAt_sin (a * t) |>.comp t hinner using 1 <;> ring
  have hlinear : HasDerivAt (fun y : ℝ => remainderScalar a * y)
      (remainderScalar a) t := by
    convert (hasDerivAt_id t).const_mul (remainderScalar a) using 1 <;> ring
  convert (hsin.sub hlinear).ofReal_comp using 1 <;>
    simp [periodicRemainder, periodicRemainder']

private lemma hasDerivAt_periodicRemainder' (a t : ℝ) :
    HasDerivAt (periodicRemainder' a) (periodicRemainder'' a t) t := by
  have hinner : HasDerivAt (fun y : ℝ => a * y) a t := by
    convert (hasDerivAt_id t).const_mul a using 1 <;> ring
  have hcos : HasDerivAt (fun y : ℝ => a * Real.cos (a * y))
      (-a ^ 2 * Real.sin (a * t)) t := by
    convert (Real.hasDerivAt_cos (a * t) |>.comp t hinner).const_mul a using 1 <;> ring
  convert (hcos.sub_const (remainderScalar a)).ofReal_comp using 1 <;>
    simp [periodicRemainder', periodicRemainder'']

private lemma fourier_neg_at_neg_pi (n : ℤ) :
    @fourier (Real.pi - (-Real.pi)) (-n)
      ((-Real.pi : ℝ) : AddCircle (Real.pi - (-Real.pi))) =
        (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
  letI : Fact (0 < Real.pi - (-Real.pi)) := ⟨by linarith [Real.pi_pos]⟩
  rw [fourier_coe_apply]
  have harg :
      (2 : ℂ) * Real.pi * Complex.I * (-n : ℤ) * (-Real.pi : ℝ) /
          (Real.pi - (-Real.pi) : ℝ) =
        ((((n : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I) := by
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [harg, Complex.exp_ofReal_mul_I, Real.cos_int_mul_pi,
    Real.sin_int_mul_pi]
  simp

private lemma fourierCoeffOn_const_one (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (fun _ : ℝ => (1 : ℂ)) n = 0 := by
  have h := fourierCoeffOn_of_hasDerivAt
    (show -Real.pi < Real.pi by linarith [Real.pi_pos]) hn
    (f := fun _ : ℝ => (1 : ℂ)) (f' := fun _ : ℝ => (0 : ℂ))
    (fun t ht => hasDerivAt_const t (1 : ℂ))
    (continuous_const.intervalIntegrable _ _)
  have hzero : fourierCoeffOn
      (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (fun _ : ℝ => (0 : ℂ)) n = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp
  rw [hzero] at h
  simpa using h

private lemma fourierCoeffOn_id (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (fun t : ℝ => (t : ℂ)) n =
        Complex.I * (((-1 : ℝ) ^ n : ℝ) : ℂ) / (n : ℂ) := by
  have h := fourierCoeffOn_of_hasDerivAt
    (show -Real.pi < Real.pi by linarith [Real.pi_pos]) hn
    (f := fun t : ℝ => (t : ℂ)) (f' := fun _ : ℝ => (1 : ℂ))
    (fun t ht => (hasDerivAt_id t).ofReal_comp)
    (continuous_const.intervalIntegrable _ _)
  rw [fourierCoeffOn_const_one n hn, fourier_neg_at_neg_pi] at h
  push_cast at h ⊢
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  field_simp [Real.pi_ne_zero, hnC] at h
  apply (eq_div_iff hnC).2
  have hh := congrArg (fun z : ℂ => z * Complex.I) h
  ring_nf at hh
  simp only [Complex.I_sq] at hh
  linear_combination (-1 / 2 : ℂ) * hh

private lemma periodicRemainder'_endpoints (a : ℝ) :
    periodicRemainder' a (-Real.pi) = periodicRemainder' a Real.pi := by
  simp [periodicRemainder', Real.cos_neg]

private lemma continuous_periodicRemainder (a : ℝ) :
    Continuous (periodicRemainder a) := by
  unfold periodicRemainder remainderScalar
  fun_prop

private lemma continuous_periodicRemainder' (a : ℝ) :
    Continuous (periodicRemainder' a) := by
  unfold periodicRemainder' remainderScalar
  fun_prop

private lemma continuous_periodicRemainder'' (a : ℝ) :
    Continuous (periodicRemainder'' a) := by
  unfold periodicRemainder''
  fun_prop

private lemma fourierCoeffOn_add_continuous {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (fun t => f t + g t) n =
      fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos]) f n +
        fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos]) g n := by
  letI : Fact (0 < Real.pi - (-Real.pi)) := ⟨by linarith [Real.pi_pos]⟩
  have hfourier : Continuous (fun t : ℝ =>
      fourier (T := Real.pi - (-Real.pi)) (-n)
        (t : AddCircle (Real.pi - (-Real.pi)))) := by fun_prop
  have hfInt : IntervalIntegrable (fun t : ℝ =>
      fourier (T := Real.pi - (-Real.pi)) (-n)
        (t : AddCircle (Real.pi - (-Real.pi))) • f t)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hfourier.smul hf).intervalIntegrable _ _
  have hgInt : IntervalIntegrable (fun t : ℝ =>
      fourier (T := Real.pi - (-Real.pi)) (-n)
        (t : AddCircle (Real.pi - (-Real.pi))) • g t)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hfourier.smul hg).intervalIntegrable _ _
  simp only [fourierCoeffOn_eq_integral, smul_add]
  rw [intervalIntegral.integral_add hfInt hgInt, smul_add]

private lemma fourierCoeffOn_periodicRemainder_second (a : ℝ) (n : ℤ) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (periodicRemainder'' a) n =
      (-(a : ℂ) ^ 2) *
          fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
            (periodicRemainder a) n +
        (-(a : ℂ) ^ 2 * (remainderScalar a : ℂ)) *
          fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
            (fun t : ℝ => (t : ℂ)) n := by
  have hdecomp : periodicRemainder'' a = fun t : ℝ =>
      (-(a : ℂ) ^ 2) * periodicRemainder a t +
        (-(a : ℂ) ^ 2 * (remainderScalar a : ℂ)) * (t : ℂ) := by
    funext t
    apply Complex.ext <;>
      simp [periodicRemainder, periodicRemainder'', remainderScalar] <;> ring
  have hcont1 : Continuous (fun t : ℝ =>
      (-(a : ℂ) ^ 2) * periodicRemainder a t) :=
    continuous_const.mul (continuous_periodicRemainder a)
  have hcont2 : Continuous (fun t : ℝ =>
      (-(a : ℂ) ^ 2 * (remainderScalar a : ℂ)) * (t : ℂ)) := by fun_prop
  rw [hdecomp, fourierCoeffOn_add_continuous hcont1 hcont2]
  rw [fourierCoeffOn.const_mul, fourierCoeffOn.const_mul]

private lemma fourierCoeffOn_periodicRemainder_ne_zero (a : ℝ)
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (periodicRemainder a) n =
      Complex.I *
        (((remainderScalar a * a ^ 2 * (-1 : ℝ) ^ n : ℝ) : ℂ) /
          ((n : ℂ) * ((n : ℂ) ^ 2 - (a : ℂ) ^ 2))) := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hplusR : (n : ℝ) + a ≠ 0 := by
    intro h
    apply ha (-n)
    push_cast
    linarith
  have hminusR : (n : ℝ) - a ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (ha n))
  have hdenR : (n : ℝ) ^ 2 - a ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplusR hminusR
  have hdenC : (n : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hdenR
  have h1 := fourierCoeffOn_of_hasDerivAt hab hn
    (f := periodicRemainder a) (f' := periodicRemainder' a)
    (fun t ht => hasDerivAt_periodicRemainder a t)
    ((continuous_periodicRemainder' a).intervalIntegrable _ _)
  have h2 := fourierCoeffOn_of_hasDerivAt hab hn
    (f := periodicRemainder' a) (f' := periodicRemainder'' a)
    (fun t ht => hasDerivAt_periodicRemainder' a t)
    ((continuous_periodicRemainder'' a).intervalIntegrable _ _)
  have hend : periodicRemainder a Real.pi -
      periodicRemainder a (-Real.pi) = 0 :=
    sub_eq_zero.mpr (periodicRemainder_endpoints a).symm
  have hend' : periodicRemainder' a Real.pi -
      periodicRemainder' a (-Real.pi) = 0 :=
    sub_eq_zero.mpr (periodicRemainder'_endpoints a).symm
  rw [hend, mul_zero, zero_sub] at h1
  rw [hend', mul_zero, zero_sub] at h2
  push_cast at h1 h2
  have h1' : Complex.I * (n : ℂ) *
      fourierCoeffOn hab (periodicRemainder a) n =
        fourierCoeffOn hab (periodicRemainder' a) n := by
    rw [h1]
    field_simp [Real.pi_ne_zero, hnC, Complex.I_ne_zero]
    ring
  have h2' : Complex.I * (n : ℂ) *
      fourierCoeffOn hab (periodicRemainder' a) n =
        fourierCoeffOn hab (periodicRemainder'' a) n := by
    rw [h2]
    field_simp [Real.pi_ne_zero, hnC, Complex.I_ne_zero]
    ring
  have h12 : (n : ℂ) ^ 2 * fourierCoeffOn hab (periodicRemainder a) n =
      -fourierCoeffOn hab (periodicRemainder'' a) n := by
    have hh := congrArg (fun z : ℂ => Complex.I * (n : ℂ) * z) h1'
    dsimp only at hh
    rw [h2'] at hh
    ring_nf at hh ⊢
    simp only [Complex.I_sq] at hh
    linear_combination -hh
  rw [fourierCoeffOn_periodicRemainder_second,
    fourierCoeffOn_id n hn] at h12
  field_simp [hnC, hdenC]
  field_simp [hnC] at h12
  push_cast at h12 ⊢
  linear_combination h12

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private lemma fourierCoeff_remainderCircle_eq (a : ℝ) (n : ℤ) :
    fourierCoeff (remainderCircle a) n =
      fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (periodicRemainder a) n := by
  change fourierCoeff (AddCircle.liftIoc (2 * Real.pi) (-Real.pi)
      (periodicRemainder a)) n = _
  rw [fourierCoeff_liftIoc_eq]
  congr 2
  ring


private def remainderCoeff (a : ℝ) (n : ℤ) : ℂ :=
  Complex.I *
    (((remainderScalar a * a ^ 2 * (-1 : ℝ) ^ n : ℝ) : ℂ) /
      ((n : ℂ) * ((n : ℂ) ^ 2 - (a : ℂ) ^ 2)))

private lemma fourierCoeffOn_periodicRemainder_zero (a : ℝ) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (periodicRemainder a) 0 = 0 := by
  have hodd (t : ℝ) :
      periodicRemainder a (-t) = -periodicRemainder a t := by
    norm_cast
    simp [periodicRemainder, remainderScalar, mul_neg, Real.sin_neg]
    ring
  have hcomp :
      (∫ t in -Real.pi..Real.pi, periodicRemainder a (-t)) =
        ∫ t in -Real.pi..Real.pi, periodicRemainder a t := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := periodicRemainder a) (a := -Real.pi) (b := Real.pi))
  have hneg :
      (∫ t in -Real.pi..Real.pi, periodicRemainder a (-t)) =
        -(∫ t in -Real.pi..Real.pi, periodicRemainder a t) := by
    calc
      (∫ t in -Real.pi..Real.pi, periodicRemainder a (-t)) =
          ∫ t in -Real.pi..Real.pi, -periodicRemainder a t := by
            apply intervalIntegral.integral_congr
            intro t ht
            exact hodd t
      _ = -(∫ t in -Real.pi..Real.pi, periodicRemainder a t) := by
        rw [intervalIntegral.integral_neg]
  have hint :
      (∫ t in -Real.pi..Real.pi, periodicRemainder a t) = 0 :=
    CharZero.eq_neg_self_iff.mp (hcomp.symm.trans hneg)
  rw [fourierCoeffOn_eq_integral]
  simp [hint, fourier_zero]

private lemma fourierCoeffOn_periodicRemainder_eq (a : ℝ)
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) (n : ℤ) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (periodicRemainder a) n = remainderCoeff a n := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_periodicRemainder_zero]
    simp [remainderCoeff]
  · simpa [remainderCoeff] using
      fourierCoeffOn_periodicRemainder_ne_zero a ha n hn

private theorem summable_remainderCoeff (a : ℝ)
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) :
    Summable (remainderCoeff a) := by
  let C : ℂ :=
    -Complex.I * (remainderScalar a : ℂ) * (a : ℂ) ^ 2
  have hbase :=
    EisensteinSeries.summable_linear_sub_mul_linear_add (a : ℂ) 1 1
  have hscaled := hbase.mul_left C
  have hnorm : Summable (fun n : ℤ =>
      ‖C * (((a : ℂ) - (n : ℂ)) * ((a : ℂ) + (n : ℂ)))⁻¹‖) := by
    simpa only [Int.cast_one, one_mul] using
      (summable_norm_iff.mpr hscaled)
  apply hnorm.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp [remainderCoeff]
    positivity
  · have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have ha_n : a ≠ (n : ℝ) := ha n
    have ha_neg_n : a ≠ -(n : ℝ) := by
      simpa using ha (-n)
    have hminus : (a : ℂ) - (n : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr ha_n
    have hplus : (a : ℂ) + (n : ℂ) ≠ 0 := by
      exact_mod_cast (by
        intro h
        apply ha_neg_n
        linarith : a + (n : ℝ) ≠ 0)
    have hden : (n : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by simpa [add_comm] using hplus)
        (by exact_mod_cast sub_ne_zero.mpr ha_n.symm)
    have hfactor :
        remainderCoeff a n =
          (C * (((a : ℂ) - (n : ℂ)) *
            ((a : ℂ) + (n : ℂ)))⁻¹) *
              ((-1 : ℂ) ^ n / (n : ℂ)) := by
      unfold remainderCoeff C
      push_cast
      field_simp [hnC, hminus, hplus, hden]
      ring
    rw [hfactor, norm_mul]
    have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn
    have hosc : ‖(-1 : ℂ) ^ n / (n : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_zpow, norm_neg, norm_one, one_zpow,
        Complex.norm_intCast]
      exact (div_le_one (by positivity)).2 hnabs
    exact mul_le_of_le_one_right (norm_nonneg _) hosc

private theorem hasSum_remainder_fourier
    (a x : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ))
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun n : ℤ =>
        remainderCoeff a n *
          fourier n ((x : ℝ) : AddCircle (2 * Real.pi)))
      (periodicRemainder a x) := by
  let F : C(AddCircle (2 * Real.pi), ℂ) := remainderCircle a
  have hcoeff : ∀ n : ℤ, fourierCoeff F n = remainderCoeff a n := by
    intro n
    calc
      fourierCoeff F n =
          fourierCoeffOn
            (show -Real.pi < Real.pi by linarith [Real.pi_pos])
            (periodicRemainder a) n := by
              exact fourierCoeff_remainderCircle_eq a n
      _ = remainderCoeff a n :=
        fourierCoeffOn_periodicRemainder_eq a ha n
  have hsummable : Summable (fourierCoeff F) :=
    (summable_remainderCoeff a ha).congr (fun n => (hcoeff n).symm)
  have hs :=
    has_pointwise_sum_fourier_series_of_summable hsummable
      ((x : ℝ) : AddCircle (2 * Real.pi))
  simp_rw [hcoeff, smul_eq_mul] at hs
  have hxmem : x ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    constructor
    · exact hx₀
    · convert hx₁.le using 1 <;> ring
  have hF :
      F ((x : ℝ) : AddCircle (2 * Real.pi)) =
        periodicRemainder a x := by
    change AddCircle.liftIoc (2 * Real.pi) (-Real.pi)
        (periodicRemainder a)
          ((x : ℝ) : AddCircle (2 * Real.pi)) =
      periodicRemainder a x
    rw [AddCircle.liftIoc_coe_apply hxmem]
  rw [hF] at hs
  exact hs

private theorem remainderCoeff_neg (a : ℝ) (n : ℤ) :
    remainderCoeff a (-n) = -remainderCoeff a n := by
  simp only [remainderCoeff, Int.cast_neg, neg_sq, zpow_neg]
  have hsign :
      ((-1 : ℝ) ^ n)⁻¹ = (-1 : ℝ) ^ n := by
    simp only [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  rw [hsign]
  push_cast
  rw [show -(n : ℂ) * ((n : ℂ) ^ 2 - (a : ℂ) ^ 2) =
      -((n : ℂ) * ((n : ℂ) ^ 2 - (a : ℂ) ^ 2)) by ring,
    div_neg]
  ring

private theorem fourier_sub_pair (n : ℕ) (x : ℝ) :
    fourier (n : ℤ)
          ((x : ℝ) : AddCircle (2 * Real.pi)) -
        fourier (-(n : ℤ))
          ((x : ℝ) : AddCircle (2 * Real.pi)) =
      (2 * Complex.I * Real.sin ((n : ℝ) * x) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  push_cast
  have hpos :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (x : ℂ) / (2 * (Real.pi : ℂ)) =
        (n : ℂ) * (x : ℂ) * Complex.I := by
    field_simp [Real.pi_ne_zero]
  have hneg :
      2 * (Real.pi : ℂ) * Complex.I * (-(n : ℂ)) *
          (x : ℂ) / (2 * (Real.pi : ℂ)) =
        -((n : ℂ) * (x : ℂ) * Complex.I) := by
    field_simp [Real.pi_ne_zero]
  rw [hpos, hneg]
  rw [Complex.exp_mul_I,
    show -((n : ℂ) * (x : ℂ) * Complex.I) =
      (-((n : ℂ) * (x : ℂ))) * Complex.I by ring,
    Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

private theorem hasSum_remainder_tail
    (a x : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ))
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun k : ℕ =>
        2 * remainderScalar a * a ^ 2 * (-1 : ℝ) ^ (k + 2) *
          Real.sin ((k + 1 : ℝ) * x) /
            ((k + 1 : ℝ) *
              ((k + 1 : ℝ) ^ 2 - a ^ 2)))
      (Real.sin (a * x) - remainderScalar a * x) := by
  have hp := (hasSum_remainder_fourier a x ha hx₀ hx₁).nat_add_neg
  have ht := (hasSum_nat_add_iff' 1).mpr hp
  have hc :
      HasSum
        (fun k : ℕ =>
          ((2 * remainderScalar a * a ^ 2 * (-1 : ℝ) ^ (k + 2) *
            Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) *
                ((k + 1 : ℝ) ^ 2 - a ^ 2)) : ℝ) : ℂ))
        (periodicRemainder a x) := by
    convert ht using 1
    · funext k
      rw [remainderCoeff_neg]
      push_cast
      have hpair := fourier_sub_pair (k + 1) x
      push_cast at hpair
      rw [show
          remainderCoeff a ((k : ℤ) + 1) *
                fourier ((k : ℤ) + 1)
                  ((x : ℝ) : AddCircle (2 * Real.pi)) +
              -remainderCoeff a ((k : ℤ) + 1) *
                fourier (-((k : ℤ) + 1))
                  ((x : ℝ) : AddCircle (2 * Real.pi)) =
            remainderCoeff a ((k : ℤ) + 1) *
              (fourier ((k : ℤ) + 1)
                  ((x : ℝ) : AddCircle (2 * Real.pi)) -
                fourier (-((k : ℤ) + 1))
                  ((x : ℝ) : AddCircle (2 * Real.pi))) by ring,
        hpair]
      unfold remainderCoeff
      push_cast
      have hk_ne : (k : ℂ) + 1 ≠ 0 := by
        exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
      have ha_nat : a ≠ (k : ℝ) + 1 := by
        simpa using ha ((k : ℤ) + 1)
      have ha_neg_nat : a ≠ -((k : ℝ) + 1) := by
        simpa using ha (-((k : ℤ) + 1))
      have hdenR : ((k : ℝ) + 1) ^ 2 - a ^ 2 ≠ 0 := by
        rw [sq_sub_sq]
        exact mul_ne_zero (by
          intro h
          apply ha_neg_nat
          linarith) (sub_ne_zero.mpr ha_nat.symm)
      have hdenC : ((k : ℂ) + 1) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast hdenR
      field_simp [hk_ne, hdenC]
      rw [Complex.I_sq]
      rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
        zpow_natCast]
      ring
    · simp [remainderCoeff]
  have hr := Complex.reCLM.hasSum hc
  simpa only [Complex.reCLM_apply, Complex.ofReal_re,
    Complex.sub_re, periodicRemainder] using hr

private theorem hasSum_sine_series
    (a x : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ))
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    ProofGap.SeriesHasSum
      (fun k : ℕ =>
        2 * Real.sin (a * Real.pi) / Real.pi *
          ((-1 : ℝ) ^ (k + 2) *
            ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) ^ 2 - a ^ 2))))
      (Real.sin (a * x)) := by
  have hrem :
      HasSum
        (fun k : ℕ =>
          2 * remainderScalar a * a ^ 2 * (-1 : ℝ) ^ (k + 2) *
            Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) *
                ((k + 1 : ℝ) ^ 2 - a ^ 2)))
        (Real.sin (a * x) - remainderScalar a * x)
        (SummationFilter.conditional ℕ) :=
    (hasSum_remainder_tail a x ha hx₀ hx₁).mono_left
      (SummationFilter.conditional ℕ).le_atTop
  have hsaw :=
    (sawtooth_series_hasSum hx₀ hx₁).mul_left
      (2 * remainderScalar a)
  have hsum := hrem.add hsaw
  have hseries :
      HasSum
        (fun k : ℕ =>
          2 * Real.sin (a * Real.pi) / Real.pi *
            ((-1 : ℝ) ^ (k + 2) *
              ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
                ((k + 1 : ℝ) ^ 2 - a ^ 2))))
        ((Real.sin (a * x) - remainderScalar a * x) +
          2 * remainderScalar a * (x / 2))
        (SummationFilter.conditional ℕ) := by
    refine hsum.congr_fun ?_
    intro k
    have hn : (k + 1 : ℝ) ≠ 0 := by positivity
    have ha_nat : a ≠ (k : ℝ) + 1 := by
      simpa using ha ((k : ℤ) + 1)
    have ha_neg_nat : a ≠ -((k : ℝ) + 1) := by
      simpa using ha (-((k : ℤ) + 1))
    have hden : ((k : ℝ) + 1) ^ 2 - a ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by
        intro h
        apply ha_neg_nat
        linarith) (sub_ne_zero.mpr ha_nat.symm)
    unfold remainderScalar
    field_simp [hn, hden, Real.pi_ne_zero]
    ring
  change HasSum
    (fun k : ℕ =>
      2 * Real.sin (a * Real.pi) / Real.pi *
        ((-1 : ℝ) ^ (k + 2) *
          ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
            ((k + 1 : ℝ) ^ 2 - a ^ 2))))
    (Real.sin (a * x)) (SummationFilter.conditional ℕ)
  convert hseries using 1 <;> ring

private theorem integral_cos_mul (c : ℝ) (hc : c ≠ 0) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos (c * x)) =
      Real.sin (c * Real.pi) / c := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.sin (c * y) / c)
        (Real.cos (c * x)) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id x).const_mul c
    convert
      ((Real.hasDerivAt_sin (c * x)).comp x hinner).div_const c using 1
    field_simp [hc]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable
        0 Real.pi)]
  simp

private theorem sin_nat_add_mul_pi (a : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) + a) * Real.pi) =
      (-1 : ℝ) ^ n * Real.sin (a * Real.pi) := by
  rw [add_mul, Real.sin_add, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  ring

private theorem sin_nat_sub_mul_pi (a : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) - a) * Real.pi) =
      -(-1 : ℝ) ^ n * Real.sin (a * Real.pi) := by
  rw [sub_mul, Real.sin_sub, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  ring

theorem gap1 (a : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sin (a * x)) :
    Function.Odd f := by
  intro x
  rw [hf, hf]
  simp

theorem gap2 (c : ℕ → ℝ) (hc : ∀ n, c n = 0) :
    ∀ n : ℕ, c 0 = c n := by
  intro n
  rw [hc 0, hc n]

theorem gap3 (c : ℕ → ℝ) (hc : ∀ n, c 0 = c n)
    (hc0 : c 0 = 0) :
    ∀ n : ℕ, c n = 0 := by
  intro n
  rw [← hc n, hc0]

theorem gap4 (c : ℕ → ℝ) (hc : ∀ n, c n = 0) :
    c 0 = 0 := by
  exact hc 0

theorem gap5 (a : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n := by
  exact hs

theorem gap6 (a : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      coefficientIntegral a n = productToSumIntegral a n := by
  intro n hn
  have hint :
      (∫ x in (0 : ℝ)..Real.pi,
        (Real.cos (((n : ℝ) - a) * x) -
          Real.cos (((n : ℝ) + a) * x))) =
        2 * ∫ x in (0 : ℝ)..Real.pi,
          Real.sin (a * x) * Real.sin ((n : ℝ) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  unfold coefficientIntegral productToSumIntegral
  rw [hint]
  ring

theorem gap7 (a : ℝ) (ha : Nonintegral a) :
    ∀ n : ℕ, 1 ≤ n →
      productToSumIntegral a n =
        2 * Real.sin (a * Real.pi) / Real.pi *
          (((-1 : ℝ) ^ (n + 1) * (n : ℝ)) /
            ((n : ℝ) ^ 2 - a ^ 2)) := by
  intro n hn
  have ha_nat : a ≠ (n : ℝ) := by
    simpa using ha (n : ℤ)
  have ha_neg_nat : a ≠ -(n : ℝ) := by
    simpa using ha (-(n : ℤ))
  have hplus : (n : ℝ) + a ≠ 0 := by
    intro h
    apply ha_neg_nat
    linarith
  have hminus : (n : ℝ) - a ≠ 0 :=
    sub_ne_zero.mpr ha_nat.symm
  have hden : (n : ℝ) ^ 2 - a ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  have hintMinus :
      IntervalIntegrable (fun x : ℝ =>
        Real.cos (((n : ℝ) - a) * x))
        MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hintPlus :
      IntervalIntegrable (fun x : ℝ =>
        Real.cos (((n : ℝ) + a) * x))
        MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  unfold productToSumIntegral
  rw [intervalIntegral.integral_sub hintMinus hintPlus,
    integral_cos_mul ((n : ℝ) - a) hminus,
    integral_cos_mul ((n : ℝ) + a) hplus,
    sin_nat_sub_mul_pi a n, sin_nat_add_mul_pi a n]
  rw [pow_succ]
  field_simp [Real.pi_ne_zero, hplus, hminus, hden]
  ring

theorem gap8 (a : ℝ) (s : ℕ → ℝ) (ha : Nonintegral a)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      s n =
        2 * Real.sin (a * Real.pi) / Real.pi *
          (((-1 : ℝ) ^ (n + 1) * (n : ℝ)) /
            ((n : ℝ) ^ 2 - a ^ 2)) := by
  intro n hn
  rw [hs n hn, gap6 a n hn, gap7 a ha n hn]

/- Duplicate of the private Fourier helper block above; retained as inactive
   text to preserve the worker's proof history without redeclaring names.
private lemma one_add_exp_mul_I (x : ℝ) :
    (1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I) =
      ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
        Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, sub_zero, zero_mul]
    rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
    ring_nf
  · simp only [Complex.add_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, zero_mul, zero_add]
    rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]
    ring_nf

private lemma one_add_exp_mul_I_ne_zero {x : ℝ}
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    (1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := by
  rw [one_add_exp_mul_I]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (by
      have := Real.cos_pos_of_mem_Ioo (x := x / 2) ⟨by linarith, by linarith⟩
      positivity))
    (Complex.exp_ne_zero _)

private lemma log_one_add_exp_mul_I_im {x : ℝ}
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    (Complex.log ((1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I))).im = x / 2 := by
  have hcos : 0 < 2 * Real.cos (x / 2) := by
    have := Real.cos_pos_of_mem_Ioo (x := x / 2) ⟨by linarith, by linarith⟩
    positivity
  rw [one_add_exp_mul_I,
    Complex.log_ofReal_mul hcos (Complex.exp_ne_zero _), Complex.add_im,
    Complex.ofReal_im, zero_add, Complex.log_exp]
  · simp
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, sub_zero]
    norm_num
    linarith [Real.pi_pos]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, sub_zero]
    norm_num
    linarith [Real.pi_pos]

private lemma complex_sawtooth_limit {x : ℝ}
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        (1 / (k + 1 : ℝ)) •
          (-(-Complex.exp ((x : ℂ) * Complex.I)) ^ (k + 1)))
      Filter.atTop
      (nhds (Complex.log ((1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I)))) := by
  let e : ℂ := Complex.exp ((x : ℂ) * Complex.I)
  let q : ℂ := -e
  let c : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  let z : ℕ → ℂ := fun k => -(q ^ (k + 1))
  have he_norm : ‖e‖ = 1 := by
    simpa [e] using Complex.norm_exp_ofReal_mul_I x
  have hq_norm : ‖q‖ = 1 := by simp [q, he_norm]
  have hq : q ≠ 1 := by
    intro h
    apply one_add_exp_mul_I_ne_zero hx₀ hx₁
    calc
      (1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I) = 1 - q := by simp [q, e]
      _ = 0 := by rw [h]; ring
  have hc_anti : Antitone c := by
    intro m n hmn
    dsimp [c]
    gcongr
  have hc_zero : Filter.Tendsto c Filter.atTop (nhds 0) := by
    simpa [c] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hz_bound : ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N, z k‖ ≤ 2 / ‖q - 1‖ := by
    intro N
    have hsum :
        (∑ k ∈ Finset.range N, z k) =
          -(∑ k ∈ Finset.range N, q ^ k) * q := by
      simp only [z, pow_succ]
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
      ring
    rw [hsum, geom_sum_eq hq, norm_mul, norm_neg, hq_norm,
      mul_one, norm_div]
    gcongr
    calc
      ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hq_norm]; norm_num
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete
    (hc_anti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      hc_zero hz_bound)
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  rw [Filter.tendsto_map'_iff] at habel
  change Filter.Tendsto
    (fun r : ℝ => ∑' k : ℕ, (c k • z k) * (r : ℂ) ^ k)
    (nhdsWithin 1 (Set.Iio 1)) (nhds l) at habel
  have hslit : (1 : ℂ) + e ∈ Complex.slitPlane := by
    rw [show (1 : ℂ) + e =
      ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
        Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) by
          simpa [e] using one_add_exp_mul_I x]
    rw [Complex.mem_slitPlane_iff]
    left
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.exp_ofReal_mul_I_re]
    have hcpos := Real.cos_pos_of_mem_Ioo (x := x / 2)
      ⟨by linarith, by linarith⟩
    positivity
  have hlimit : Filter.Tendsto
      (fun r : ℝ =>
        Complex.log ((1 : ℂ) + (r : ℂ) * e) / (r : ℂ))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (Complex.log ((1 : ℂ) + e))) := by
    have harg : ContinuousAt
        (fun r : ℝ => (1 : ℂ) + (r : ℂ) * e) 1 := by fun_prop
    have hlog := (harg.clog (by simpa using hslit)).tendsto
    have hcoe : ContinuousAt (fun r : ℝ => (r : ℂ)) 1 := by fun_prop
    have hdiv := hlog.div hcoe.tendsto (by norm_num)
    simpa using hdiv.mono_left inf_le_left
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1),
      (∑' k : ℕ, (c k • z k) * (r : ℂ) ^ k) =
        Complex.log ((1 : ℂ) + (r : ℂ) * e) / (r : ℂ) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hrnorm : ‖(r : ℂ) * e‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, he_norm,
        mul_one, abs_of_pos hr.1]
      exact hr.2
    have htaylor := Complex.hasSum_taylorSeries_log hrnorm
    have htail := (hasSum_nat_add_iff' 1).mpr htaylor
    simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, sub_zero] at htail
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.1.ne'
    have hscaled := htail.div_const (r : ℂ)
    calc
      (∑' k : ℕ, (c k • z k) * (r : ℂ) ^ k) =
          ∑' k : ℕ,
            (-1 : ℂ) ^ (k + 1 + 1) * ((r : ℂ) * e) ^ (k + 1) /
              (k + 1 : ℕ) / (r : ℂ) := by
        apply tsum_congr
        intro k
        dsimp [c, z, q]
        have hkR : (k : ℝ) + 1 ≠ 0 := by positivity
        have hkC : (k : ℂ) + 1 ≠ 0 := by
          intro h
          have hre := congrArg Complex.re h
          simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
            Complex.zero_re] at hre
          have : 0 < (k : ℝ) + 1 := by positivity
          linarith
        simp only [one_div, Complex.ofReal_inv, Nat.cast_add, Nat.cast_one]
        field_simp [hkR, hkC, hr0]
        rw [mul_pow]
        push_cast
        ring_nf
      _ = Complex.log ((1 : ℂ) + (r : ℂ) * e) / (r : ℂ) := hscaled.tsum_eq
  have habel' := habel.congr' heq
  exact (tendsto_nhds_unique habel' hlimit) ▸ hl

private lemma complex_sawtooth_term_im (x : ℝ) (k : ℕ) :
    (((1 / (k + 1 : ℝ)) •
      (-(-Complex.exp ((x : ℂ) * Complex.I)) ^ (k + 1)) : ℂ)).im =
      (-1 : ℝ) ^ (k + 2) * Real.sin ((k + 1 : ℝ) * x) /
        (k + 1 : ℝ) := by
  let e : ℂ := Complex.exp ((x : ℂ) * Complex.I)
  have hepow : (e ^ (k + 1)).im = Real.sin ((k + 1 : ℝ) * x) := by
    rw [← Complex.exp_nat_mul]
    have harg : (((k + 1 : ℕ) : ℂ)) * ((x : ℂ) * Complex.I) =
        ((((k + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_im]
    norm_num
  have hz : -(-e) ^ (k + 1) =
      (-1 : ℂ) ^ (k + 2) * e ^ (k + 1) := by
    rw [show -e = (-1 : ℂ) * e by ring, mul_pow,
      show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  rw [show Complex.exp ((x : ℂ) * Complex.I) = e by rfl, hz]
  have hsignRe : ((-1 : ℂ) ^ (k + 2)).re = (-1 : ℝ) ^ (k + 2) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  have hsignIm : ((-1 : ℂ) ^ (k + 2)).im = 0 := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_pow, Complex.ofReal_im]
  rw [Complex.smul_im, Complex.mul_im, hsignRe, hsignIm, hepow]
  simp only [zero_mul, add_zero, smul_eq_mul]
  ring

private lemma sawtooth_series_hasSum {x : ℝ}
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    ProofGap.SeriesHasSum
      (fun k : ℕ =>
        (-1 : ℝ) ^ (k + 2) * Real.sin ((k + 1 : ℝ) * x) /
          (k + 1 : ℝ))
      (x / 2) := by
  have hcomplex := complex_sawtooth_limit hx₀ hx₁
  have him := (Complex.imCLM.continuous.tendsto _).comp hcomplex
  change Filter.Tendsto
    (fun N : ℕ =>
      (∑ k ∈ Finset.range N,
        (1 / (k + 1 : ℝ)) •
          (-(-Complex.exp ((x : ℂ) * Complex.I)) ^ (k + 1))).im)
    Filter.atTop
    (nhds (Complex.log ((1 : ℂ) +
      Complex.exp ((x : ℂ) * Complex.I))).im) at him
  rw [log_one_add_exp_mul_I_im hx₀ hx₁] at him
  unfold ProofGap.SeriesHasSum HasSum
  rw [SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  change Filter.Tendsto
    (fun N : ℕ => ∑ k ∈ Finset.range N,
      (-1 : ℝ) ^ (k + 2) * Real.sin ((k + 1 : ℝ) * x) /
        (k + 1 : ℝ))
    Filter.atTop (nhds (x / 2))
  apply him.congr'
  filter_upwards with N
  change Complex.imCLM
      (∑ k ∈ Finset.range N,
        (1 / (k + 1 : ℝ)) •
          (-(-Complex.exp ((x : ℂ) * Complex.I)) ^ (k + 1))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact complex_sawtooth_term_im x k

private def remainderScalar (a : ℝ) : ℝ :=
  Real.sin (a * Real.pi) / Real.pi

private def periodicRemainder (a t : ℝ) : ℂ :=
  (Real.sin (a * t) - remainderScalar a * t : ℝ)

private def periodicRemainder' (a t : ℝ) : ℂ :=
  (a * Real.cos (a * t) - remainderScalar a : ℝ)

private def periodicRemainder'' (a t : ℝ) : ℂ :=
  (-a ^ 2 * Real.sin (a * t) : ℝ)

private lemma periodicRemainder_endpoints (a : ℝ) :
    periodicRemainder a (-Real.pi) = periodicRemainder a Real.pi := by
  unfold periodicRemainder remainderScalar
  rw [mul_neg, Real.sin_neg]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

private noncomputable def remainderCircle (a : ℝ) :
    C(AddCircle (2 * Real.pi), ℂ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact
    { toFun := AddCircle.liftIoc (2 * Real.pi) (-Real.pi)
        (periodicRemainder a)
      continuous_toFun := by
        apply AddCircle.liftIoc_continuous
        · convert periodicRemainder_endpoints a using 1 <;> ring
        · unfold periodicRemainder
          fun_prop }

private lemma hasDerivAt_periodicRemainder (a t : ℝ) :
    HasDerivAt (periodicRemainder a) (periodicRemainder' a t) t := by
  have hinner : HasDerivAt (fun y : ℝ => a * y) a t := by
    convert (hasDerivAt_id t).const_mul a using 1 <;> ring
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (a * y))
      (a * Real.cos (a * t)) t := by
    convert Real.hasDerivAt_sin (a * t) |>.comp t hinner using 1 <;> ring
  have hlinear : HasDerivAt (fun y : ℝ => remainderScalar a * y)
      (remainderScalar a) t := by
    convert (hasDerivAt_id t).const_mul (remainderScalar a) using 1 <;> ring
  convert (hsin.sub hlinear).ofReal_comp using 1 <;>
    simp [periodicRemainder, periodicRemainder']

private lemma hasDerivAt_periodicRemainder' (a t : ℝ) :
    HasDerivAt (periodicRemainder' a) (periodicRemainder'' a t) t := by
  have hinner : HasDerivAt (fun y : ℝ => a * y) a t := by
    convert (hasDerivAt_id t).const_mul a using 1 <;> ring
  have hcos : HasDerivAt (fun y : ℝ => a * Real.cos (a * y))
      (-a ^ 2 * Real.sin (a * t)) t := by
    convert (Real.hasDerivAt_cos (a * t) |>.comp t hinner).const_mul a using 1 <;> ring
  convert (hcos.sub_const (remainderScalar a)).ofReal_comp using 1 <;>
    simp [periodicRemainder', periodicRemainder'']

private lemma fourier_neg_at_neg_pi (n : ℤ) :
    @fourier (Real.pi - (-Real.pi)) (-n)
      ((-Real.pi : ℝ) : AddCircle (Real.pi - (-Real.pi))) =
        (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
  letI : Fact (0 < Real.pi - (-Real.pi)) := ⟨by linarith [Real.pi_pos]⟩
  rw [fourier_coe_apply]
  have harg :
      (2 : ℂ) * Real.pi * Complex.I * (-n : ℤ) * (-Real.pi : ℝ) /
          (Real.pi - (-Real.pi) : ℝ) =
        ((((n : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I) := by
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [harg, Complex.exp_ofReal_mul_I, Real.cos_int_mul_pi,
    Real.sin_int_mul_pi]
  simp

private lemma fourierCoeffOn_const_one (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (fun _ : ℝ => (1 : ℂ)) n = 0 := by
  have h := fourierCoeffOn_of_hasDerivAt
    (show -Real.pi < Real.pi by linarith [Real.pi_pos]) hn
    (f := fun _ : ℝ => (1 : ℂ)) (f' := fun _ : ℝ => (0 : ℂ))
    (fun t ht => hasDerivAt_const t (1 : ℂ))
    (continuous_const.intervalIntegrable _ _)
  have hzero : fourierCoeffOn
      (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (fun _ : ℝ => (0 : ℂ)) n = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp
  rw [hzero] at h
  simpa using h

private lemma fourierCoeffOn_id (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (fun t : ℝ => (t : ℂ)) n =
        Complex.I * (((-1 : ℝ) ^ n : ℝ) : ℂ) / (n : ℂ) := by
  have h := fourierCoeffOn_of_hasDerivAt
    (show -Real.pi < Real.pi by linarith [Real.pi_pos]) hn
    (f := fun t : ℝ => (t : ℂ)) (f' := fun _ : ℝ => (1 : ℂ))
    (fun t ht => (hasDerivAt_id t).ofReal_comp)
    (continuous_const.intervalIntegrable _ _)
  rw [fourierCoeffOn_const_one n hn, fourier_neg_at_neg_pi] at h
  push_cast at h ⊢
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  field_simp [Real.pi_ne_zero, hnC] at h
  apply (eq_div_iff hnC).2
  have hh := congrArg (fun z : ℂ => z * Complex.I) h
  ring_nf at hh
  simp only [Complex.I_sq] at hh
  linear_combination (-1 / 2 : ℂ) * hh

private lemma periodicRemainder'_endpoints (a : ℝ) :
    periodicRemainder' a (-Real.pi) = periodicRemainder' a Real.pi := by
  simp [periodicRemainder', Real.cos_neg]

private lemma continuous_periodicRemainder (a : ℝ) :
    Continuous (periodicRemainder a) := by
  unfold periodicRemainder remainderScalar
  fun_prop

private lemma continuous_periodicRemainder' (a : ℝ) :
    Continuous (periodicRemainder' a) := by
  unfold periodicRemainder' remainderScalar
  fun_prop

private lemma continuous_periodicRemainder'' (a : ℝ) :
    Continuous (periodicRemainder'' a) := by
  unfold periodicRemainder''
  fun_prop

private lemma fourierCoeffOn_add_continuous {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (fun t => f t + g t) n =
      fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos]) f n +
        fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos]) g n := by
  letI : Fact (0 < Real.pi - (-Real.pi)) := ⟨by linarith [Real.pi_pos]⟩
  have hfourier : Continuous (fun t : ℝ =>
      fourier (T := Real.pi - (-Real.pi)) (-n)
        (t : AddCircle (Real.pi - (-Real.pi)))) := by fun_prop
  have hfInt : IntervalIntegrable (fun t : ℝ =>
      fourier (T := Real.pi - (-Real.pi)) (-n)
        (t : AddCircle (Real.pi - (-Real.pi))) • f t)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hfourier.smul hf).intervalIntegrable _ _
  have hgInt : IntervalIntegrable (fun t : ℝ =>
      fourier (T := Real.pi - (-Real.pi)) (-n)
        (t : AddCircle (Real.pi - (-Real.pi))) • g t)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hfourier.smul hg).intervalIntegrable _ _
  simp only [fourierCoeffOn_eq_integral, smul_add]
  rw [intervalIntegral.integral_add hfInt hgInt, smul_add]

private lemma fourierCoeffOn_periodicRemainder_second (a : ℝ) (n : ℤ) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (periodicRemainder'' a) n =
      (-(a : ℂ) ^ 2) *
          fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
            (periodicRemainder a) n +
        (-(a : ℂ) ^ 2 * (remainderScalar a : ℂ)) *
          fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
            (fun t : ℝ => (t : ℂ)) n := by
  have hdecomp : periodicRemainder'' a = fun t : ℝ =>
      (-(a : ℂ) ^ 2) * periodicRemainder a t +
        (-(a : ℂ) ^ 2 * (remainderScalar a : ℂ)) * (t : ℂ) := by
    funext t
    apply Complex.ext <;>
      simp [periodicRemainder, periodicRemainder'', remainderScalar] <;> ring
  have hcont1 : Continuous (fun t : ℝ =>
      (-(a : ℂ) ^ 2) * periodicRemainder a t) :=
    continuous_const.mul (continuous_periodicRemainder a)
  have hcont2 : Continuous (fun t : ℝ =>
      (-(a : ℂ) ^ 2 * (remainderScalar a : ℂ)) * (t : ℂ)) := by fun_prop
  rw [hdecomp, fourierCoeffOn_add_continuous hcont1 hcont2]
  rw [fourierCoeffOn.const_mul, fourierCoeffOn.const_mul]

private lemma fourierCoeffOn_periodicRemainder_ne_zero (a : ℝ)
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (periodicRemainder a) n =
      Complex.I *
        (((remainderScalar a * a ^ 2 * (-1 : ℝ) ^ n : ℝ) : ℂ) /
          ((n : ℂ) * ((n : ℂ) ^ 2 - (a : ℂ) ^ 2))) := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hplusR : (n : ℝ) + a ≠ 0 := by
    intro h
    apply ha (-n)
    push_cast
    linarith
  have hminusR : (n : ℝ) - a ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (ha n))
  have hdenR : (n : ℝ) ^ 2 - a ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplusR hminusR
  have hdenC : (n : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hdenR
  have h1 := fourierCoeffOn_of_hasDerivAt hab hn
    (f := periodicRemainder a) (f' := periodicRemainder' a)
    (fun t ht => hasDerivAt_periodicRemainder a t)
    ((continuous_periodicRemainder' a).intervalIntegrable _ _)
  have h2 := fourierCoeffOn_of_hasDerivAt hab hn
    (f := periodicRemainder' a) (f' := periodicRemainder'' a)
    (fun t ht => hasDerivAt_periodicRemainder' a t)
    ((continuous_periodicRemainder'' a).intervalIntegrable _ _)
  have hend : periodicRemainder a Real.pi -
      periodicRemainder a (-Real.pi) = 0 :=
    sub_eq_zero.mpr (periodicRemainder_endpoints a).symm
  have hend' : periodicRemainder' a Real.pi -
      periodicRemainder' a (-Real.pi) = 0 :=
    sub_eq_zero.mpr (periodicRemainder'_endpoints a).symm
  rw [hend, mul_zero, zero_sub] at h1
  rw [hend', mul_zero, zero_sub] at h2
  push_cast at h1 h2
  have h1' : Complex.I * (n : ℂ) *
      fourierCoeffOn hab (periodicRemainder a) n =
        fourierCoeffOn hab (periodicRemainder' a) n := by
    rw [h1]
    field_simp [Real.pi_ne_zero, hnC, Complex.I_ne_zero]
    ring
  have h2' : Complex.I * (n : ℂ) *
      fourierCoeffOn hab (periodicRemainder' a) n =
        fourierCoeffOn hab (periodicRemainder'' a) n := by
    rw [h2]
    field_simp [Real.pi_ne_zero, hnC, Complex.I_ne_zero]
    ring
  have h12 : (n : ℂ) ^ 2 * fourierCoeffOn hab (periodicRemainder a) n =
      -fourierCoeffOn hab (periodicRemainder'' a) n := by
    have hh := congrArg (fun z : ℂ => Complex.I * (n : ℂ) * z) h1'
    dsimp only at hh
    rw [h2'] at hh
    ring_nf at hh ⊢
    simp only [Complex.I_sq] at hh
    linear_combination -hh
  rw [fourierCoeffOn_periodicRemainder_second,
    fourierCoeffOn_id n hn] at h12
  field_simp [hnC, hdenC]
  field_simp [hnC] at h12
  push_cast at h12 ⊢
  linear_combination h12

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private lemma fourierCoeff_remainderCircle_eq (a : ℝ) (n : ℤ) :
    fourierCoeff (remainderCircle a) n =
      fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (periodicRemainder a) n := by
  change fourierCoeff (AddCircle.liftIoc (2 * Real.pi) (-Real.pi)
      (periodicRemainder a)) n = _
  rw [fourierCoeff_liftIoc_eq]
  congr 2
  ring

private lemma fourierCoeffOn_periodicRemainder_deriv (a : ℝ)
    (n : ℤ) (hn : n ≠ 0) :
    Complex.I * (n : ℂ) *
        fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
          (periodicRemainder a) n =
      fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
        (periodicRemainder' a) n := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h := fourierCoeffOn_of_hasDerivAt hab hn
    (f := periodicRemainder a) (f' := periodicRemainder' a)
    (fun t ht => hasDerivAt_periodicRemainder a t)
    ((continuous_periodicRemainder' a).intervalIntegrable _ _)
  have hend : periodicRemainder a Real.pi -
      periodicRemainder a (-Real.pi) = 0 :=
    sub_eq_zero.mpr (periodicRemainder_endpoints a).symm
  rw [hend, mul_zero, zero_sub] at h
  push_cast at h
  rw [h]
  field_simp [Real.pi_ne_zero, hnC, Complex.I_ne_zero]
  ring

private lemma summable_fourierCoeff_remainderCircle (a : ℝ) :
    Summable (fun n : ℤ => fourierCoeff (remainderCircle a) n) := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let d : ℤ → ℂ := fun n => fourierCoeffOn hab (periodicRemainder' a) n
  have hd_memLp : MeasureTheory.MemLp (periodicRemainder' a) 2
      (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
    refine MeasureTheory.MemLp.of_bound
      (continuous_periodicRemainder' a).aestronglyMeasurable
      (|a| + |remainderScalar a|) ?_
    filter_upwards with t
    rw [show periodicRemainder' a t =
      ((a * Real.cos (a * t) - remainderScalar a : ℝ) : ℂ) by rfl,
      Complex.norm_real]
    calc
      |a * Real.cos (a * t) - remainderScalar a| ≤
          |a * Real.cos (a * t)| + |remainderScalar a| := abs_sub _ _
      _ = |a| * |Real.cos (a * t)| + |remainderScalar a| := by
        rw [abs_mul]
      _ ≤ |a| * 1 + |remainderScalar a| := by
        gcongr
        exact Real.abs_cos_le_one _
      _ = |a| + |remainderScalar a| := by ring
  have hd_sq : Summable (fun n : ℤ => ‖d n‖ ^ 2) := by
    simpa [d, hab] using (hasSum_sq_fourierCoeffOn hab hd_memLp).summable
  have hinv_sq : Summable (fun n : ℤ => (1 / |(n : ℝ)|) ^ 2) := by
    simpa only [div_pow, one_pow, sq_abs] using
      (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hmajor : Summable (fun n : ℤ =>
      (‖d n‖ ^ 2 + (1 / |(n : ℝ)|) ^ 2) / 2) :=
    (hd_sq.add hinv_sq).div_const 2
  refine hmajor.of_norm_bounded_eventually ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hn
  have hnR : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hn)
  have hrel := fourierCoeffOn_periodicRemainder_deriv a n hn
  have hnormrel : |(n : ℝ)| *
      ‖fourierCoeffOn hab (periodicRemainder a) n‖ = ‖d n‖ := by
    have h := congrArg norm hrel
    simpa [d, hab, norm_mul, mul_assoc] using h
  have hnorm : ‖fourierCoeffOn hab (periodicRemainder a) n‖ =
      ‖d n‖ / |(n : ℝ)| := by
    apply (eq_div_iff hnR).2
    simpa [mul_comm] using hnormrel
  rw [fourierCoeff_remainderCircle_eq, hnorm, div_eq_mul_inv, one_div]
  nlinarith [sq_nonneg (‖d n‖ - |(n : ℝ)|⁻¹)]

private def remainderCoeff (a : ℝ) (n : ℤ) : ℂ :=
  Complex.I *
    (((remainderScalar a * a ^ 2 * (-1 : ℝ) ^ n : ℝ) : ℂ) /
      ((n : ℂ) * ((n : ℂ) ^ 2 - (a : ℂ) ^ 2)))

private lemma fourierCoeffOn_periodicRemainder_zero (a : ℝ) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (periodicRemainder a) 0 = 0 := by
  have hodd (t : ℝ) :
      periodicRemainder a (-t) = -periodicRemainder a t := by
    norm_cast
    simp [periodicRemainder, remainderScalar, mul_neg, Real.sin_neg]
    ring
  have hcomp :
      (∫ t in -Real.pi..Real.pi, periodicRemainder a (-t)) =
        ∫ t in -Real.pi..Real.pi, periodicRemainder a t := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := periodicRemainder a) (a := -Real.pi) (b := Real.pi))
  have hneg :
      (∫ t in -Real.pi..Real.pi, periodicRemainder a (-t)) =
        -(∫ t in -Real.pi..Real.pi, periodicRemainder a t) := by
    calc
      (∫ t in -Real.pi..Real.pi, periodicRemainder a (-t)) =
          ∫ t in -Real.pi..Real.pi, -periodicRemainder a t := by
            apply intervalIntegral.integral_congr
            intro t ht
            exact hodd t
      _ = -(∫ t in -Real.pi..Real.pi, periodicRemainder a t) := by
        rw [intervalIntegral.integral_neg]
  have hint :
      (∫ t in -Real.pi..Real.pi, periodicRemainder a t) = 0 :=
    CharZero.eq_neg_self_iff.mp (hcomp.symm.trans hneg)
  rw [fourierCoeffOn_eq_integral]
  simp [hint, fourier_zero]

private lemma fourierCoeffOn_periodicRemainder_eq (a : ℝ)
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) (n : ℤ) :
    fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
      (periodicRemainder a) n = remainderCoeff a n := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_periodicRemainder_zero]
    simp [remainderCoeff]
  · simpa [remainderCoeff] using
      fourierCoeffOn_periodicRemainder_ne_zero a ha n hn

private theorem summable_remainderCoeff (a : ℝ)
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) :
    Summable (remainderCoeff a) := by
  let C : ℂ :=
    -Complex.I * (remainderScalar a : ℂ) * (a : ℂ) ^ 2
  have hbase :=
    EisensteinSeries.summable_linear_sub_mul_linear_add (a : ℂ) 1 1
  have hscaled := hbase.mul_left C
  have hnorm : Summable (fun n : ℤ =>
      ‖C * (((a : ℂ) - (n : ℂ)) * ((a : ℂ) + (n : ℂ)))⁻¹‖) := by
    simpa only [Int.cast_one, one_mul] using
      (summable_norm_iff.mpr hscaled)
  apply hnorm.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp [remainderCoeff]
    positivity
  · have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have ha_n : a ≠ (n : ℝ) := ha n
    have ha_neg_n : a ≠ -(n : ℝ) := by
      simpa using ha (-n)
    have hminus : (a : ℂ) - (n : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr ha_n
    have hplus : (a : ℂ) + (n : ℂ) ≠ 0 := by
      exact_mod_cast (by
        intro h
        apply ha_neg_n
        linarith : a + (n : ℝ) ≠ 0)
    have hden : (n : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by simpa [add_comm] using hplus)
        (by exact_mod_cast sub_ne_zero.mpr ha_n.symm)
    have hfactor :
        remainderCoeff a n =
          (C * (((a : ℂ) - (n : ℂ)) *
            ((a : ℂ) + (n : ℂ)))⁻¹) *
              ((-1 : ℂ) ^ n / (n : ℂ)) := by
      unfold remainderCoeff C
      push_cast
      field_simp [hnC, hminus, hplus, hden]
      ring
    rw [hfactor, norm_mul]
    have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn
    have hosc : ‖(-1 : ℂ) ^ n / (n : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_zpow, norm_neg, norm_one, one_zpow,
        Complex.norm_intCast]
      exact (div_le_one (by positivity)).2 hnabs
    exact mul_le_of_le_one_right (norm_nonneg _) hosc

private theorem hasSum_remainder_fourier
    (a x : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ))
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun n : ℤ =>
        remainderCoeff a n *
          fourier n ((x : ℝ) : AddCircle (2 * Real.pi)))
      (periodicRemainder a x) := by
  let F : C(AddCircle (2 * Real.pi), ℂ) := remainderCircle a
  have hcoeff : ∀ n : ℤ, fourierCoeff F n = remainderCoeff a n := by
    intro n
    calc
      fourierCoeff F n =
          fourierCoeffOn
            (show -Real.pi < Real.pi by linarith [Real.pi_pos])
            (periodicRemainder a) n := by
              exact fourierCoeff_remainderCircle_eq a n
      _ = remainderCoeff a n :=
        fourierCoeffOn_periodicRemainder_eq a ha n
  have hsummable : Summable (fourierCoeff F) :=
    (summable_remainderCoeff a ha).congr (fun n => (hcoeff n).symm)
  have hs :=
    has_pointwise_sum_fourier_series_of_summable hsummable
      ((x : ℝ) : AddCircle (2 * Real.pi))
  simp_rw [hcoeff, smul_eq_mul] at hs
  have hxmem : x ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    constructor
    · exact hx₀
    · convert hx₁.le using 1 <;> ring
  have hF :
      F ((x : ℝ) : AddCircle (2 * Real.pi)) =
        periodicRemainder a x := by
    change AddCircle.liftIoc (2 * Real.pi) (-Real.pi)
        (periodicRemainder a)
          ((x : ℝ) : AddCircle (2 * Real.pi)) =
      periodicRemainder a x
    rw [AddCircle.liftIoc_coe_apply hxmem]
  rw [hF] at hs
  exact hs

private theorem remainderCoeff_neg (a : ℝ) (n : ℤ) :
    remainderCoeff a (-n) = -remainderCoeff a n := by
  simp only [remainderCoeff, Int.cast_neg, neg_sq, zpow_neg]
  have hsign :
      ((-1 : ℝ) ^ n)⁻¹ = (-1 : ℝ) ^ n := by
    simp only [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  rw [hsign]
  push_cast
  rw [show -(n : ℂ) * ((n : ℂ) ^ 2 - (a : ℂ) ^ 2) =
      -((n : ℂ) * ((n : ℂ) ^ 2 - (a : ℂ) ^ 2)) by ring,
    div_neg]
  ring

private theorem fourier_sub_pair (n : ℕ) (x : ℝ) :
    fourier (n : ℤ)
          ((x : ℝ) : AddCircle (2 * Real.pi)) -
        fourier (-(n : ℤ))
          ((x : ℝ) : AddCircle (2 * Real.pi)) =
      (2 * Complex.I * Real.sin ((n : ℝ) * x) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  push_cast
  have hpos :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (x : ℂ) / (2 * (Real.pi : ℂ)) =
        (n : ℂ) * (x : ℂ) * Complex.I := by
    field_simp [Real.pi_ne_zero]
  have hneg :
      2 * (Real.pi : ℂ) * Complex.I * (-(n : ℂ)) *
          (x : ℂ) / (2 * (Real.pi : ℂ)) =
        -((n : ℂ) * (x : ℂ) * Complex.I) := by
    field_simp [Real.pi_ne_zero]
  rw [hpos, hneg]
  rw [Complex.exp_mul_I,
    show -((n : ℂ) * (x : ℂ) * Complex.I) =
      (-((n : ℂ) * (x : ℂ))) * Complex.I by ring,
    Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

private theorem hasSum_remainder_tail
    (a x : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ))
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun k : ℕ =>
        2 * remainderScalar a * a ^ 2 * (-1 : ℝ) ^ (k + 2) *
          Real.sin ((k + 1 : ℝ) * x) /
            ((k + 1 : ℝ) *
              ((k + 1 : ℝ) ^ 2 - a ^ 2)))
      (Real.sin (a * x) - remainderScalar a * x) := by
  have hp := (hasSum_remainder_fourier a x ha hx₀ hx₁).nat_add_neg
  have ht := (hasSum_nat_add_iff' 1).mpr hp
  have hc :
      HasSum
        (fun k : ℕ =>
          ((2 * remainderScalar a * a ^ 2 * (-1 : ℝ) ^ (k + 2) *
            Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) *
                ((k + 1 : ℝ) ^ 2 - a ^ 2)) : ℝ) : ℂ))
        (periodicRemainder a x) := by
    convert ht using 1
    · funext k
      rw [remainderCoeff_neg]
      push_cast
      have hpair := fourier_sub_pair (k + 1) x
      push_cast at hpair
      rw [show
          remainderCoeff a ((k : ℤ) + 1) *
                fourier ((k : ℤ) + 1)
                  ((x : ℝ) : AddCircle (2 * Real.pi)) +
              -remainderCoeff a ((k : ℤ) + 1) *
                fourier (-((k : ℤ) + 1))
                  ((x : ℝ) : AddCircle (2 * Real.pi)) =
            remainderCoeff a ((k : ℤ) + 1) *
              (fourier ((k : ℤ) + 1)
                  ((x : ℝ) : AddCircle (2 * Real.pi)) -
                fourier (-((k : ℤ) + 1))
                  ((x : ℝ) : AddCircle (2 * Real.pi))) by ring,
        hpair]
      unfold remainderCoeff
      push_cast
      have hk_ne : (k : ℂ) + 1 ≠ 0 := by
        exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
      have ha_nat : a ≠ (k : ℝ) + 1 := by
        simpa using ha ((k : ℤ) + 1)
      have ha_neg_nat : a ≠ -((k : ℝ) + 1) := by
        simpa using ha (-((k : ℤ) + 1))
      have hdenR : ((k : ℝ) + 1) ^ 2 - a ^ 2 ≠ 0 := by
        rw [sq_sub_sq]
        exact mul_ne_zero (by
          intro h
          apply ha_neg_nat
          linarith) (sub_ne_zero.mpr ha_nat.symm)
      have hdenC : ((k : ℂ) + 1) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast hdenR
      field_simp [hk_ne, hdenC]
      rw [Complex.I_sq]
      rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
        zpow_natCast]
      ring
    · simp [remainderCoeff]
  have hr := Complex.reCLM.hasSum hc
  simpa only [Complex.reCLM_apply, Complex.ofReal_re,
    Complex.sub_re, periodicRemainder] using hr

private theorem hasSum_sine_series
    (a x : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ))
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    ProofGap.SeriesHasSum
      (fun k : ℕ =>
        2 * Real.sin (a * Real.pi) / Real.pi *
          ((-1 : ℝ) ^ (k + 2) *
            ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) ^ 2 - a ^ 2))))
      (Real.sin (a * x)) := by
  have hrem :
      HasSum
        (fun k : ℕ =>
          2 * remainderScalar a * a ^ 2 * (-1 : ℝ) ^ (k + 2) *
            Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) *
                ((k + 1 : ℝ) ^ 2 - a ^ 2)))
        (Real.sin (a * x) - remainderScalar a * x)
        (SummationFilter.conditional ℕ) :=
    (hasSum_remainder_tail a x ha hx₀ hx₁).mono_left
      (SummationFilter.conditional ℕ).le_atTop
  have hsaw :=
    (sawtooth_series_hasSum hx₀ hx₁).mul_left
      (2 * remainderScalar a)
  have hsum := hrem.add hsaw
  have hseries :
      HasSum
        (fun k : ℕ =>
          2 * Real.sin (a * Real.pi) / Real.pi *
            ((-1 : ℝ) ^ (k + 2) *
              ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
                ((k + 1 : ℝ) ^ 2 - a ^ 2))))
        ((Real.sin (a * x) - remainderScalar a * x) +
          2 * remainderScalar a * (x / 2))
        (SummationFilter.conditional ℕ) := by
    refine hsum.congr_fun ?_
    intro k
    have hn : (k + 1 : ℝ) ≠ 0 := by positivity
    have ha_nat : a ≠ (k : ℝ) + 1 := by
      simpa using ha ((k : ℤ) + 1)
    have ha_neg_nat : a ≠ -((k : ℝ) + 1) := by
      simpa using ha (-((k : ℤ) + 1))
    have hden : ((k : ℝ) + 1) ^ 2 - a ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by
        intro h
        apply ha_neg_nat
        linarith) (sub_ne_zero.mpr ha_nat.symm)
    unfold remainderScalar
    field_simp [hn, hden, Real.pi_ne_zero]
    ring
  change HasSum
    (fun k : ℕ =>
      2 * Real.sin (a * Real.pi) / Real.pi *
        ((-1 : ℝ) ^ (k + 2) *
          ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
            ((k + 1 : ℝ) ^ 2 - a ^ 2))))
    (Real.sin (a * x)) (SummationFilter.conditional ℕ)
  convert hseries using 1 <;> ring

-/

theorem gap9 (a : ℝ) (f : ℝ → ℝ) (ha : Nonintegral a)
    (hf : ∀ x, f x = Real.sin (a * x)) :
    ∀ x, -Real.pi < x → x < Real.pi →
      ProofGap.SeriesHasSum
        (fun k : ℕ =>
          2 * Real.sin (a * Real.pi) / Real.pi *
            (((-1 : ℝ) ^ (k + 2) * (k + 1 : ℝ) *
              Real.sin ((k + 1 : ℝ) * x)) /
              ((k + 1 : ℝ) ^ 2 - a ^ 2)))
        (f x) := by
  intro x hx₀ hx₁
  rw [hf]
  have hs := hasSum_sine_series a x ha hx₀ hx₁
  refine hs.congr_fun ?_
  intro k
  ring

theorem gap10 (a x : ℝ) (ha : Nonintegral a)
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    ProofGap.SeriesHasSum
      (fun k : ℕ =>
        2 * Real.sin (a * Real.pi) / Real.pi *
          (((-1 : ℝ) ^ (k + 2) * (k + 1 : ℝ) *
            Real.sin ((k + 1 : ℝ) * x)) /
            ((k + 1 : ℝ) ^ 2 - a ^ 2)))
      (Real.sin (a * x)) := by
  have hs := hasSum_sine_series a x ha hx₀ hx₁
  refine hs.congr_fun ?_
  intro k
  ring

theorem gap11 (a : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sin (a * x)) :
    ∀ x, f x = Real.sin (a * x) := by
  exact hf

end

end ProofGap.Exercise2946
