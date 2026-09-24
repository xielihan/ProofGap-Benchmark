import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace ProofGap.Exercise3023

noncomputable section

open scoped BigOperators

def alternatingSineSeries (x : ℝ) : ℝ :=
  ∑'[SummationFilter.conditional ℕ] n : ℕ,
    (-1 : ℝ) ^ (n + 1) *
      Real.sin (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ)

def alternatingCosineSeries (x : ℝ) : ℝ :=
  ∑'[SummationFilter.conditional ℕ] n : ℕ,
    (-1 : ℝ) ^ (n + 1) *
      Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ)

def targetSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    (-1 : ℝ) ^ (n + 2) *
      Real.cos (((n + 2 : ℕ) : ℝ) * x) /
        ((((n + 2 : ℕ) : ℝ) ^ 2) - 1)

private theorem shifted_log_hasSum {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum
      (fun n : ℕ => w ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      (-Complex.log (1 - w)) := by
  simpa using
    (hasSum_nat_add_iff' 1).mpr
      (Complex.hasSum_taylorSeries_neg_log (z := w) hw)

private theorem boundary_log_hasSum (q : ℂ) (hq : ‖q‖ = 1) (hq1 : q ≠ 1)
    (hslit : 1 - q ∈ Complex.slitPlane) :
    HasSum
      (fun n : ℕ => q ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      (-Complex.log (1 - q))
      (SummationFilter.conditional ℕ) := by
  let a : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  let z : ℕ → ℂ := fun n => q ^ (n + 1)
  have ha : Antitone a := by
    intro m n hmn
    dsimp [a]
    gcongr
  have ha0 : Tendsto a atTop (nhds 0) := by
    simpa only [a, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hqsub : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq1)
  have hz : ∀ N : ℕ, ‖∑ i ∈ Finset.range N, z i‖ ≤ 2 / ‖q - 1‖ := by
    intro N
    have hsum :
        (∑ i ∈ Finset.range N, z i) =
          q * ∑ i ∈ Finset.range N, q ^ i := by
      dsimp [z]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ']
    rw [hsum, geom_sum_eq hq1, norm_mul, hq, one_mul, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hq]; norm_num
  have hc := ha.cauchySeq_series_mul_of_tendsto_zero_of_bounded ha0 hz
  have hc' :
      CauchySeq
        (fun N =>
          ∑ i ∈ Finset.range N,
            q ^ (i + 1) / ((i + 1 : ℕ) : ℂ)) := by
    convert hc using 1
    funext N
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a, z]
    change
      q ^ (i + 1) / ((i + 1 : ℕ) : ℂ) =
        (((1 / ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) * q ^ (i + 1))
    push_cast
    ring
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hc'
  have hscond :
      HasSum
        (fun n : ℕ => q ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
        s (SummationFilter.conditional ℕ) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff]
    simpa [Function.comp_def] using hs
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hs
  rw [Filter.tendsto_map'_iff] at hab
  change Tendsto
      (fun r : ℝ =>
        ∑' n : ℕ,
          (q ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds s) at hab
  have heq : ∀ᶠ r : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      (∑' n : ℕ,
        (q ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n) =
        (r : ℂ)⁻¹ * (-Complex.log (1 - (r : ℂ) * q)) := by
    filter_upwards
      [(eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        inf_le_left, self_mem_nhdsWithin] with r hr (hr1 : r < 1)
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    have hw : ‖(r : ℂ) * q‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hq,
        mul_one]
      exact hr1
    have hsum := (shifted_log_hasSum hw).mul_left (r : ℂ)⁻¹
    calc
      (∑' n : ℕ,
        (q ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n) =
          ∑' n : ℕ,
            (r : ℂ)⁻¹ *
              (((r : ℂ) * q) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
        apply tsum_congr
        intro n
        rw [mul_pow]
        field_simp [hr0]
        rw [pow_succ]
        ring
      _ = _ := hsum.tsum_eq
  have hi : ContinuousAt (fun r : ℝ => (r : ℂ)⁻¹) 1 := by
    exact Complex.continuous_ofReal.continuousAt.inv₀ (by norm_num)
  have hwcont : ContinuousAt (fun r : ℝ => (r : ℂ) * q) 1 := by
    fun_prop
  have hl :
      ContinuousAt (fun r : ℝ => Complex.log (1 - (r : ℂ) * q)) 1 := by
    exact (continuousAt_const.sub hwcont).clog (by simpa using hslit)
  have hlim :
      Tendsto
        (fun r : ℝ => (r : ℂ)⁻¹ * (-Complex.log (1 - (r : ℂ) * q)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (-Complex.log (1 - q))) := by
    simpa only [Pi.mul_apply, Pi.neg_apply, Complex.ofReal_one, inv_one,
      one_mul] using
      (hi.mul hl.neg).tendsto.mono_left
        (show nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds 1 from inf_le_left)
  have hab' :
      Tendsto
        (fun r : ℝ => (r : ℂ)⁻¹ * (-Complex.log (1 - (r : ℂ) * q)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds s) :=
    hab.congr' heq
  have hsq : s = -Complex.log (1 - q) :=
    tendsto_nhds_unique hab' hlim
  simpa [hsq] using hscond

private theorem alternating_complex_num (x : ℝ) (n : ℕ) :
    (-Complex.exp ((x : ℂ) * Complex.I)) ^ (n + 1) =
      Complex.ofReal ((-1 : ℝ) ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * x)) +
        Complex.ofReal ((-1 : ℝ) ^ (n + 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * x)) * Complex.I := by
  rw [neg_pow, ← Complex.exp_nat_mul]
  have harg :
      ((n + 1 : ℕ) : ℂ) * ((x : ℂ) * Complex.I) =
        (((((n + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  push_cast
  ring

private theorem alternating_complex_term_re (x : ℝ) (n : ℕ) :
    ((-Complex.exp ((x : ℂ) * Complex.I)) ^ (n + 1) /
        ((n + 1 : ℕ) : ℂ)).re =
      (-1 : ℝ) ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ) := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [alternating_complex_num, Complex.div_re]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, Complex.natCast_re, Complex.natCast_im, zero_mul,
    Complex.normSq_natCast]
  field_simp
  ring

private theorem alternating_complex_term_im (x : ℝ) (n : ℕ) :
    ((-Complex.exp ((x : ℂ) * Complex.I)) ^ (n + 1) /
        ((n + 1 : ℕ) : ℂ)).im =
      (-1 : ℝ) ^ (n + 1) *
        Real.sin (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ) := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [alternating_complex_num, Complex.div_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_add, Complex.natCast_re, Complex.natCast_im, zero_mul,
    Complex.normSq_natCast]
  field_simp
  ring

private theorem alternating_complex_hasSum (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    HasSum
      (fun n : ℕ =>
        (-Complex.exp ((x : ℂ) * Complex.I)) ^ (n + 1) /
          ((n + 1 : ℕ) : ℂ))
      (-(Real.log (2 * Real.cos (x / 2)) : ℂ) -
        (((x / 2 : ℝ) : ℂ) * Complex.I))
      (SummationFilter.conditional ℕ) := by
  let q : ℂ := -Complex.exp ((x : ℂ) * Complex.I)
  have hcos : 0 < Real.cos (x / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2]
  have hqnorm : ‖q‖ = 1 := by
    simp [q, Complex.norm_exp_ofReal_mul_I]
  have hq1 : q ≠ 1 := by
    intro h
    have : (1 - q).re = 0 := by rw [h]; norm_num
    dsimp [q] at this
    simp only [sub_neg_eq_add, Complex.add_re, Complex.one_re,
      Complex.exp_ofReal_mul_I_re] at this
    have hpos : 0 < 1 + Real.cos x := by
      calc
        0 < 2 * Real.cos (x / 2) ^ 2 := by positivity
        _ = 1 + Real.cos x := by
          rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
          ring
    linarith
  have hslit : 1 - q ∈ Complex.slitPlane := by
    left
    dsimp [q]
    simp only [sub_neg_eq_add, Complex.add_re, Complex.one_re,
      Complex.exp_ofReal_mul_I_re]
    calc
      0 < 2 * Real.cos (x / 2) ^ 2 := by positivity
      _ = 1 + Real.cos x := by
        rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
        ring
  have hfactor :
      (1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I) =
        ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
          Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re,
        Complex.exp_ofReal_mul_I_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      calc
        1 + Real.cos x = 1 + Real.cos (2 * (x / 2)) := by congr 2 <;> ring
        _ = 2 * Real.cos (x / 2) * Real.cos (x / 2) := by
          rw [Real.cos_two_mul]
          ring
    · simp only [Complex.add_im, Complex.one_im, zero_add,
        Complex.exp_ofReal_mul_I_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, add_zero]
      calc
        Real.sin x = Real.sin (2 * (x / 2)) := by congr 1 <;> ring
        _ = 2 * Real.cos (x / 2) * Real.sin (x / 2) := by
          rw [Real.sin_two_mul]
          ring
  have hlogexp :
      Complex.log (Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I)) =
        (((x / 2 : ℝ) : ℂ) * Complex.I) := by
    apply Complex.log_exp
    · simp
      linarith [hx.1, Real.pi_pos]
    · simp
      linarith [hx.2, Real.pi_pos]
  have hlog :
      Complex.log (1 - q) =
        (Real.log (2 * Real.cos (x / 2)) : ℂ) +
          (((x / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [show 1 - q =
      ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
        Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) by
          simpa [q] using hfactor]
    rw [Complex.log_ofReal_mul (mul_pos (by norm_num) hcos)
      (Complex.exp_ne_zero _), hlogexp]
  have hs := boundary_log_hasSum q hqnorm hq1 hslit
  rw [hlog] at hs
  convert hs using 1 <;> simp [q] <;> ring

theorem gap1 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    alternatingSineSeries x = -x / 2 := by
  have hs := Complex.hasSum_im (alternating_complex_hasSum x hx)
  have hs' :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ))
        (-x / 2) (SummationFilter.conditional ℕ) := by
    convert hs using 1
    · funext n
      exact (alternating_complex_term_im x n).symm
    · simp
      ring
  simpa [alternatingSineSeries] using hs'.tsum_eq

theorem gap2 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    alternatingCosineSeries x =
      -Real.log (2 * Real.cos (x / 2)) := by
  have hs := Complex.hasSum_re (alternating_complex_hasSum x hx)
  have hs' :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 1) *
            Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ))
        (-Real.log (2 * Real.cos (x / 2)))
        (SummationFilter.conditional ℕ) := by
    convert hs using 1
    · funext n
      exact (alternating_complex_term_re x n).symm
    · simp
  simpa [alternatingCosineSeries] using hs'.tsum_eq

theorem gap3 (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / ((n : ℝ) ^ 2 - 1) =
      (1 / 2 : ℝ) * (1 / ((n : ℝ) - 1) - 1 / ((n : ℝ) + 1)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm : (n : ℝ) - 1 ≠ 0 := by nlinarith
  have hp : (n : ℝ) + 1 ≠ 0 := by nlinarith
  have hd : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

private theorem hasSum_to_conditional {f : ℕ → ℝ} {s : ℝ}
    (h : HasSum f s) :
    HasSum f s (SummationFilter.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def] using h.tendsto_sum_nat

private theorem conditional_hasSum_shift_two {f : ℕ → ℝ} {s : ℝ}
    (h : HasSum f s (SummationFilter.conditional ℕ)) :
    HasSum (fun n => f (n + 2)) (s - f 0 - f 1)
      (SummationFilter.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff] at h ⊢
  change Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (nhds s) at h
  change Tendsto (fun N => ∑ n ∈ Finset.range N, f (n + 2)) atTop
    (nhds (s - f 0 - f 1))
  have hshift := h.comp (Filter.tendsto_add_atTop_nat 2)
  change Tendsto (fun N => ∑ n ∈ Finset.range (N + 2), f n) atTop
    (nhds s) at hshift
  have hconst :
      Tendsto (fun _ : ℕ => f 0 + f 1) atTop (nhds (f 0 + f 1)) :=
    tendsto_const_nhds
  convert hshift.sub hconst using 1
  · funext N
    induction N with
    | zero => simp [Finset.sum_range_succ]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih,
          show Nat.succ N + 2 = (N + 2) + 1 by omega,
          Finset.sum_range_succ]
        rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ]
        have hrange :
            (∑ x ∈ Finset.range (3 + N), f x) =
              (∑ x ∈ Finset.range N, f x) + f N + f (N + 1) + f (N + 2) := by
          rw [show 3 + N = ((N + 1) + 1) + 1 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_succ]
        rw [show N + 1 + 1 + 1 = 3 + N by omega, hrange,
          show N + 1 + 1 = N + 2 by omega]
        ring
  · ring

private theorem alternating_sine_hasSum (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    HasSum
      (fun n : ℕ =>
        (-1 : ℝ) ^ (n + 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ))
      (-x / 2) (SummationFilter.conditional ℕ) := by
  have hs := Complex.hasSum_im (alternating_complex_hasSum x hx)
  convert hs using 1
  · funext n
    exact (alternating_complex_term_im x n).symm
  · simp
    ring

private theorem alternating_cosine_hasSum (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    HasSum
      (fun n : ℕ =>
        (-1 : ℝ) ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ))
      (-Real.log (2 * Real.cos (x / 2)))
      (SummationFilter.conditional ℕ) := by
  have hs := Complex.hasSum_re (alternating_complex_hasSum x hx)
  convert hs using 1
  · funext n
    exact (alternating_complex_term_re x n).symm
  · simp

private theorem shifted_cosine_plus_hasSum (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    HasSum
      (fun n : ℕ =>
        (-1 : ℝ) ^ (n + 1) *
          Real.cos (((n + 2 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ))
      (Real.cos x * (-Real.log (2 * Real.cos (x / 2))) -
        Real.sin x * (-x / 2))
      (SummationFilter.conditional ℕ) := by
  have h :=
    ((alternating_cosine_hasSum x hx).mul_left (Real.cos x)).sub
      ((alternating_sine_hasSum x hx).mul_left (Real.sin x))
  convert h using 1
  funext n
  have harg :
      (((n + 2 : ℕ) : ℝ) * x) =
        (((n + 1 : ℕ) : ℝ) * x) + x := by
    push_cast
    ring
  rw [harg, Real.cos_add]
  ring

private theorem shifted_cosine_minus_hasSum (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    HasSum
      (fun n : ℕ =>
        (-1 : ℝ) ^ (n + 1) * Real.cos ((n : ℝ) * x) /
          ((n + 1 : ℕ) : ℝ))
      (Real.cos x * (-Real.log (2 * Real.cos (x / 2))) +
        Real.sin x * (-x / 2))
      (SummationFilter.conditional ℕ) := by
  have h :=
    ((alternating_cosine_hasSum x hx).mul_left (Real.cos x)).add
      ((alternating_sine_hasSum x hx).mul_left (Real.sin x))
  convert h using 1
  funext n
  have harg :
      ((n : ℝ) * x) = (((n + 1 : ℕ) : ℝ) * x) - x := by
    push_cast
    ring
  rw [harg, Real.cos_sub]
  ring

private theorem cosine_difference_hasSum (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    HasSum
      (fun n : ℕ =>
        (-1 : ℝ) ^ (n + 1) *
          (Real.cos ((n : ℝ) * x) -
            Real.cos (((n + 2 : ℕ) : ℝ) * x)) /
          ((n + 1 : ℕ) : ℝ))
      (-x * Real.sin x) (SummationFilter.conditional ℕ) := by
  have h :=
    ((alternating_sine_hasSum x hx).mul_right (Real.sin x)).mul_left 2
  convert h using 1
  · funext n
    have hm :
        ((n : ℝ) * x) = (((n + 1 : ℕ) : ℝ) * x) - x := by
      push_cast
      ring
    have hp :
        (((n + 2 : ℕ) : ℝ) * x) =
          (((n + 1 : ℕ) : ℝ) * x) + x := by
      push_cast
      ring
    rw [hm, hp, Real.cos_sub, Real.cos_add]
    ring
  · ring

private theorem target_summable (x : ℝ) :
    Summable
      (fun n : ℕ =>
        (-1 : ℝ) ^ (n + 2) *
          Real.cos (((n + 2 : ℕ) : ℝ) * x) /
            ((((n + 2 : ℕ) : ℝ) ^ 2) - 1)) := by
  have hp :
      Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [Function.comp_def] using
      ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).comp_injective
        Nat.succ_injective
  refine hp.of_norm_bounded ?_
  intro n
  have hden :
      ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) =
        ((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ) := by
    push_cast
    ring
  have h1 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have h3 : 0 < ((n + 3 : ℕ) : ℝ) := by positivity
  rw [hden, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_pos (mul_pos h1 h3)]
  calc
    |Real.cos (((n + 2 : ℕ) : ℝ) * x)| /
          (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) ≤
        1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) := by
      gcongr
      exact Real.abs_cos_le_one _
    _ ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
      gcongr
      push_cast
      nlinarith

theorem gap4 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    targetSeries x =
      (1 / 2 : ℝ) *
        (∑'[SummationFilter.conditional ℕ] n : ℕ,
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) /
              (((n + 2 : ℕ) : ℝ) - 1)) -
      (1 / 2 : ℝ) *
        (∑'[SummationFilter.conditional ℕ] n : ℕ,
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) /
              (((n + 2 : ℕ) : ℝ) + 1)) := by
  have hplus := shifted_cosine_plus_hasSum x hx
  have hp :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ))
        (-(Real.cos x * (-Real.log (2 * Real.cos (x / 2))) -
          Real.sin x * (-x / 2)))
        (SummationFilter.conditional ℕ) := by
    convert hplus.neg using 1
    funext n
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    push_cast
    ring
  have hminus := shifted_cosine_minus_hasSum x hx
  have htail := conditional_hasSum_shift_two hminus
  let sq : ℝ :=
    -(Real.cos x * (-Real.log (2 * Real.cos (x / 2))) +
      Real.sin x * (-x / 2) -
      ((-1 : ℝ) ^ (0 + 1) * Real.cos ((0 : ℝ) * x) / (0 + 1)) -
      ((-1 : ℝ) ^ (1 + 1) * Real.cos ((1 : ℝ) * x) / (1 + 1)))
  have hq :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) / ((n + 3 : ℕ) : ℝ))
        sq
        (SummationFilter.conditional ℕ) := by
    dsimp [sq]
    convert htail.neg using 1
    · funext n
      rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
      push_cast
      ring
    · norm_num
  have hcomb :=
    (hp.summable.hasSum.mul_left (1 / 2 : ℝ)).sub
      (hq.summable.hasSum.mul_left (1 / 2 : ℝ))
  have hcomb' :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) /
              ((((n + 2 : ℕ) : ℝ) ^ 2) - 1))
        ((1 / 2 : ℝ) *
          (∑'[SummationFilter.conditional ℕ] n : ℕ,
            (-1 : ℝ) ^ (n + 2) *
              Real.cos (((n + 2 : ℕ) : ℝ) * x) /
                (((n + 2 : ℕ) : ℝ) - 1)) -
        (1 / 2 : ℝ) *
          (∑'[SummationFilter.conditional ℕ] n : ℕ,
            (-1 : ℝ) ^ (n + 2) *
              Real.cos (((n + 2 : ℕ) : ℝ) * x) /
                (((n + 2 : ℕ) : ℝ) + 1)))
        (SummationFilter.conditional ℕ) := by
    convert hcomb using 1
    · funext n
      have hpf := gap3 (n + 2) (by omega)
      push_cast at hpf ⊢
      calc
        _ = ((-1 : ℝ) ^ (n + 2) * Real.cos (((n : ℝ) + 2) * x)) *
            (1 / (((n : ℝ) + 2) ^ 2 - 1)) := by ring
        _ = ((-1 : ℝ) ^ (n + 2) * Real.cos (((n : ℝ) + 2) * x)) *
            ((1 / 2 : ℝ) *
              (1 / ((n : ℝ) + 2 - 1) - 1 / ((n : ℝ) + 2 + 1))) := by
          rw [hpf]
        _ = _ := by ring
    · apply congrArg₂ (fun u v : ℝ => (1 / 2 : ℝ) * u - (1 / 2 : ℝ) * v)
      · apply tsum_congr
        intro n
        push_cast
        ring
      · apply tsum_congr
        intro n
        push_cast
        ring
  have ht :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) /
              ((((n + 2 : ℕ) : ℝ) ^ 2) - 1))
        (targetSeries x) (SummationFilter.conditional ℕ) := by
    apply hasSum_to_conditional
    simpa [targetSeries] using (target_summable x).hasSum
  calc
    targetSeries x =
        ∑'[SummationFilter.conditional ℕ] n : ℕ,
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) /
              ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) := ht.tsum_eq.symm
    _ = _ := hcomb'.tsum_eq

theorem gap5 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    targetSeries x =
      -(1 / 2 : ℝ) *
        (∑'[SummationFilter.conditional ℕ] m : ℕ,
          (-1 : ℝ) ^ (m + 1) *
            Real.cos (((m + 2 : ℕ) : ℝ) * x) / ((m + 1 : ℕ) : ℝ)) +
      (1 / 2 : ℝ) *
        (∑'[SummationFilter.conditional ℕ] m : ℕ,
          (-1 : ℝ) ^ (m + 3) *
            Real.cos (((m + 2 : ℕ) : ℝ) * x) / ((m + 3 : ℕ) : ℝ)) := by
  have ha := shifted_cosine_plus_hasSum x hx
  have hb := conditional_hasSum_shift_two (shifted_cosine_minus_hasSum x hx)
  have hcomb :=
    (ha.summable.hasSum.mul_left (-(1 / 2 : ℝ))).add
      (hb.summable.hasSum.mul_left (1 / 2 : ℝ))
  have hcomb' :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) /
              ((((n + 2 : ℕ) : ℝ) ^ 2) - 1))
        (-(1 / 2 : ℝ) *
          (∑'[SummationFilter.conditional ℕ] m : ℕ,
            (-1 : ℝ) ^ (m + 1) *
              Real.cos (((m + 2 : ℕ) : ℝ) * x) / ((m + 1 : ℕ) : ℝ)) +
        (1 / 2 : ℝ) *
          (∑'[SummationFilter.conditional ℕ] m : ℕ,
            (-1 : ℝ) ^ (m + 3) *
              Real.cos (((m + 2 : ℕ) : ℝ) * x) / ((m + 3 : ℕ) : ℝ)))
        (SummationFilter.conditional ℕ) := by
    convert hcomb using 1
    · funext n
      have hpf := gap3 (n + 2) (by omega)
      push_cast at hpf ⊢
      calc
        _ = ((-1 : ℝ) ^ (n + 2) * Real.cos (((n : ℝ) + 2) * x)) *
            (1 / (((n : ℝ) + 2) ^ 2 - 1)) := by ring
        _ = ((-1 : ℝ) ^ (n + 2) * Real.cos (((n : ℝ) + 2) * x)) *
            ((1 / 2 : ℝ) *
              (1 / ((n : ℝ) + 2 - 1) - 1 / ((n : ℝ) + 2 + 1))) := by
          rw [hpf]
        _ = _ := by
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ,
            show n + 3 = (n + 1) + 2 by omega, pow_add]
          norm_num
          ring
  have ht :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) /
              ((((n + 2 : ℕ) : ℝ) ^ 2) - 1))
        (targetSeries x) (SummationFilter.conditional ℕ) := by
    apply hasSum_to_conditional
    simpa [targetSeries] using (target_summable x).hasSum
  calc
    targetSeries x =
        ∑'[SummationFilter.conditional ℕ] n : ℕ,
          (-1 : ℝ) ^ (n + 2) *
            Real.cos (((n + 2 : ℕ) : ℝ) * x) /
              ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) := ht.tsum_eq.symm
    _ = _ := hcomb'.tsum_eq

theorem gap6 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    targetSeries x =
      (1 / 2 : ℝ) *
        (∑'[SummationFilter.conditional ℕ] m : ℕ,
          (-1 : ℝ) ^ (m + 1) *
            (Real.cos ((m : ℝ) * x) -
              Real.cos (((m + 2 : ℕ) : ℝ) * x)) /
            ((m + 1 : ℕ) : ℝ)) -
      (-(1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.cos x) := by
  rw [gap5 x hx]
  have ha := shifted_cosine_plus_hasSum x hx
  have hb := conditional_hasSum_shift_two (shifted_cosine_minus_hasSum x hx)
  have hd := cosine_difference_hasSum x hx
  rw [ha.tsum_eq, hb.tsum_eq, hd.tsum_eq]
  norm_num
  ring

theorem gap7 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    targetSeries x =
      (1 / 2 : ℝ) * (1 - Real.cos x / 2) +
      ∑'[SummationFilter.conditional ℕ] m : ℕ,
        (-1 : ℝ) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) *
          Real.sin (((m + 1 : ℕ) : ℝ) * x) * Real.sin x := by
  rw [gap6 x hx]
  have hd := cosine_difference_hasSum x hx
  have hs := (alternating_sine_hasSum x hx).mul_right (Real.sin x)
  have hs' :
      HasSum
        (fun m : ℕ =>
          (-1 : ℝ) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) *
            Real.sin (((m + 1 : ℕ) : ℝ) * x) * Real.sin x)
        ((-x / 2) * Real.sin x) (SummationFilter.conditional ℕ) := by
    convert hs using 1
    funext m
    ring
  rw [hd.tsum_eq, hs'.tsum_eq]
  ring

theorem gap8 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    (1 / 2 : ℝ) * (1 - Real.cos x / 2) +
        (∑'[SummationFilter.conditional ℕ] m : ℕ,
          (-1 : ℝ) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) *
            Real.sin (((m + 1 : ℕ) : ℝ) * x) * Real.sin x) =
      (1 / 2 : ℝ) * (1 - Real.cos x / 2) - x / 2 * Real.sin x := by
  have hs := (alternating_sine_hasSum x hx).mul_right (Real.sin x)
  have hs' :
      HasSum
        (fun m : ℕ =>
          (-1 : ℝ) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) *
            Real.sin (((m + 1 : ℕ) : ℝ) * x) * Real.sin x)
        ((-x / 2) * Real.sin x) (SummationFilter.conditional ℕ) := by
    convert hs using 1
    funext m
    ring
  rw [hs'.tsum_eq]
  ring

private def cg (w : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    ((w⁻¹ - w) * Complex.log (1 - w) + 1 + w / 2)

private theorem complex_hasSum {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    HasSum
      (fun n : ℕ =>
        w ^ (n + 2) /
          ((((n + 2 : ℕ) : ℂ) ^ 2) - 1))
      (cg w) := by
  have hlog := Complex.hasSum_taylorSeries_neg_log (z := w) hw
  have hA0 :
      HasSum (fun n : ℕ => w ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
        (-Complex.log (1 - w)) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hlog
  have hA :
      HasSum (fun n : ℕ => w ^ (n + 2) / ((n + 1 : ℕ) : ℂ))
        (w * (-Complex.log (1 - w))) := by
    refine (hA0.mul_left w).congr ?_
    intro n
    simp only [pow_succ']
    push_cast
    ring_nf
  have hB0 :
      HasSum (fun n : ℕ => w ^ (n + 3) / ((n + 3 : ℕ) : ℂ))
        (-Complex.log (1 - w) - (w + w ^ 2 / 2)) := by
    convert (hasSum_nat_add_iff' 3).mpr hlog using 1
    norm_num [Finset.sum_range_succ]
  have hB :
      HasSum (fun n : ℕ => w ^ (n + 2) / ((n + 3 : ℕ) : ℂ))
        (w⁻¹ * (-Complex.log (1 - w) - (w + w ^ 2 / 2))) := by
    refine (hB0.mul_left w⁻¹).congr ?_
    intro n
    simp only [pow_succ']
    field_simp [hw0]
  convert (hA.sub hB).mul_left (1 / 2 : ℂ) using 1
  · funext n
    have hn1 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      norm_cast
    have hn3 : (((n + 3 : ℕ) : ℂ)) ≠ 0 := by
      norm_cast
    have hden :
        ((((n + 2 : ℕ) : ℂ) ^ 2) - 1) =
          (((n + 1 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ)) := by
      push_cast
      ring
    rw [hden]
    field_simp
    push_cast
    ring_nf
  · unfold cg
    field_simp [hw0]
    ring_nf

private theorem complex_summable (q : ℂ) (hq : ‖q‖ ≤ 1) :
    Summable
      (fun n : ℕ =>
        q ^ (n + 2) /
          ((((n + 2 : ℕ) : ℂ) ^ 2) - 1)) := by
  have hp :
      Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [Function.comp_def] using
      ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).comp_injective
        Nat.succ_injective
  refine hp.of_norm_bounded ?_
  intro n
  have hden :
      ((((n + 2 : ℕ) : ℂ) ^ 2) - 1) =
        (((n + 1 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ)) := by
    push_cast
    ring
  rw [hden, norm_div, norm_pow, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast]
  have hpow : ‖q‖ ^ (n + 2) ≤ 1 := pow_le_one₀ (norm_nonneg q) hq
  have h1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have h3 : (0 : ℝ) < (n + 3 : ℕ) := by positivity
  calc
    ‖q‖ ^ (n + 2) / ((n + 1 : ℕ) * (n + 3 : ℕ)) ≤
        1 / ((n + 1 : ℕ) * (n + 3 : ℕ)) := by
      gcongr
    _ ≤ 1 / ((n + 1 : ℕ) ^ 2) := by
      gcongr
      push_cast
      nlinarith

private theorem complex_tsum_eq_cg (q : ℂ) (hq : ‖q‖ = 1)
    (hslit : 1 - q ∈ Complex.slitPlane) :
    (∑' n : ℕ,
      q ^ (n + 2) /
        ((((n + 2 : ℕ) : ℂ) ^ 2) - 1)) =
      cg q := by
  let f : ℕ → ℂ := fun n =>
    q ^ (n + 2) /
      ((((n + 2 : ℕ) : ℂ) ^ 2) - 1)
  have hf : Summable f := complex_summable q hq.le
  have hab :=
    Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
      hf.hasSum.tendsto_sum_nat
  rw [Filter.tendsto_map'_iff] at hab
  change Tendsto
      (fun r : ℝ => ∑' n : ℕ, f n * (r : ℂ) ^ n)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (∑' n : ℕ, f n)) at hab
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
  have heq : ∀ᶠ r : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      (∑' n : ℕ, f n * (r : ℂ) ^ n) =
        ((r : ℂ)⁻¹ ^ 2) * cg ((r : ℂ) * q) := by
    filter_upwards
      [(eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        inf_le_left, self_mem_nhdsWithin] with r hr (hr1 : r < 1)
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    have hw0 : (r : ℂ) * q ≠ 0 := mul_ne_zero hr0 hq0
    have hw : ‖(r : ℂ) * q‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hq,
        mul_one]
      exact hr1
    have hs := (complex_hasSum hw hw0).mul_left ((r : ℂ)⁻¹ ^ 2)
    calc
      (∑' n : ℕ, f n * (r : ℂ) ^ n) =
          ∑' n : ℕ,
            ((r : ℂ)⁻¹ ^ 2) *
              (((r : ℂ) * q) ^ (n + 2) /
                ((((n + 2 : ℕ) : ℂ) ^ 2) - 1)) := by
        apply tsum_congr
        intro n
        dsimp [f]
        rw [mul_pow]
        have hpow :
            (r : ℂ) ^ (n + 2) = (r : ℂ) ^ 2 * (r : ℂ) ^ n := by
          rw [show n + 2 = 2 + n by omega, pow_add]
        rw [hpow]
        field_simp [hr0]
      _ = _ := hs.tsum_eq
  have hwcont : ContinuousAt (fun r : ℝ => (r : ℂ) * q) 1 := by
    fun_prop
  have hi :
      ContinuousAt (fun r : ℝ => (((r : ℂ) * q)⁻¹)) 1 := by
    exact hwcont.inv₀ (by simpa using hq0)
  have hl :
      ContinuousAt
        (fun r : ℝ => Complex.log (1 - (r : ℂ) * q)) 1 := by
    exact (continuousAt_const.sub hwcont).clog (by simpa using hslit)
  have hcg : ContinuousAt (fun r : ℝ => cg ((r : ℂ) * q)) 1 := by
    unfold cg
    exact (((((hi.sub hwcont).mul hl).add continuousAt_const).add
      (hwcont.div_const 2)).const_mul (1 / 2 : ℂ))
  have hrinv : ContinuousAt (fun r : ℝ => ((r : ℂ)⁻¹ ^ 2)) 1 := by
    exact Complex.continuous_ofReal.continuousAt.inv₀ (by norm_num) |>.pow 2
  have hlim :
      Tendsto (fun r : ℝ => ((r : ℂ)⁻¹ ^ 2) * cg ((r : ℂ) * q))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (cg q)) := by
    simpa using (hrinv.mul hcg).tendsto.mono_left inf_le_left
  have hab' :
      Tendsto (fun r : ℝ => ((r : ℂ)⁻¹ ^ 2) * cg ((r : ℂ) * q))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (∑' n : ℕ, f n)) :=
    hab.congr' heq
  change (∑' n : ℕ, f n) = cg q
  exact tendsto_nhds_unique hab' hlim

private theorem complex_term_re (x : ℝ) (n : ℕ) :
    (((-Complex.exp ((x : ℂ) * Complex.I)) ^ (n + 2) /
      ((((n + 2 : ℕ) : ℂ) ^ 2) - 1)).re) =
      (-1 : ℝ) ^ (n + 2) *
        Real.cos (((n + 2 : ℕ) : ℝ) * x) /
          ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) := by
  have hk : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hdpos : 0 < (((n + 2 : ℕ) : ℝ) ^ 2 - 1) := by nlinarith
  have hden :
      ((((n + 2 : ℕ) : ℂ) ^ 2) - 1) =
        (((((n + 2 : ℕ) : ℝ) ^ 2) - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  have hnum :
      (-Complex.exp ((x : ℂ) * Complex.I)) ^ (n + 2) =
        (((-1 : ℝ) ^ (n + 2) : ℝ) : ℂ) *
          Complex.exp
            (((((n + 2 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
    rw [neg_pow, ← Complex.exp_nat_mul]
    congr 1
    · norm_cast
    · congr 1
      push_cast
      ring
  rw [hden, hnum, Complex.div_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, mul_zero,
    zero_mul, sub_zero, Complex.normSq_apply, add_zero]
  field_simp [ne_of_gt hdpos]
  ring

private theorem real_tsum_interior (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    (∑' n : ℕ,
      (-1 : ℝ) ^ (n + 2) *
        Real.cos (((n + 2 : ℕ) : ℝ) * x) /
          ((((n + 2 : ℕ) : ℝ) ^ 2) - 1)) =
      (1 / 2 : ℝ) * (1 - Real.cos x / 2) -
        x / 2 * Real.sin x := by
  let q : ℂ := -Complex.exp ((x : ℂ) * Complex.I)
  have hcos : 0 < Real.cos (x / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2]
  have hfactor :
      (1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I) =
        ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
          Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re,
        Complex.exp_ofReal_mul_I_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, sub_zero]
      calc
        1 + Real.cos x =
            1 + Real.cos (2 * (x / 2)) := by congr 2 <;> ring
        _ = 2 * Real.cos (x / 2) * Real.cos (x / 2) := by
          rw [Real.cos_two_mul]
          ring
    · simp only [Complex.add_im, Complex.one_im, zero_add,
        Complex.exp_ofReal_mul_I_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, add_zero]
      calc
        Real.sin x = Real.sin (2 * (x / 2)) := by congr 1 <;> ring
        _ = 2 * Real.cos (x / 2) * Real.sin (x / 2) := by
          rw [Real.sin_two_mul]
          ring
  have hqnorm : ‖q‖ = 1 := by
    simp [q, Complex.norm_exp_ofReal_mul_I]
  have hslit : 1 - q ∈ Complex.slitPlane := by
    left
    dsimp [q]
    simp only [sub_neg_eq_add, Complex.add_re, Complex.one_re,
      Complex.exp_ofReal_mul_I_re]
    calc
      0 < 2 * Real.cos (x / 2) ^ 2 := by positivity
      _ = 1 + Real.cos x := by
        rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
        ring
  have hlogexp :
      Complex.log
          (Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I)) =
        (((x / 2 : ℝ) : ℂ) * Complex.I) := by
    apply Complex.log_exp
    · simp
      linarith [hx.1, Real.pi_pos]
    · simp
      linarith [hx.2, Real.pi_pos]
  have hlog :
      Complex.log (1 - q) =
        (Real.log (2 * Real.cos (x / 2)) : ℂ) +
          (((x / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [show 1 - q =
      ((2 * Real.cos (x / 2) : ℝ) : ℂ) *
        Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) by
          simpa [q] using hfactor]
    rw [Complex.log_ofReal_mul (mul_pos (by norm_num) hcos)
      (Complex.exp_ne_zero _), hlogexp]
  have hqinv :
      q⁻¹ = -Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
    dsimp [q]
    rw [inv_neg, ← Complex.exp_neg]
    congr 2
    push_cast
    ring
  have hqdiff :
      q⁻¹ - q = ((2 * Real.sin x : ℝ) : ℂ) * Complex.I := by
    have hnegexp :
        Complex.exp (((-x : ℝ) : ℂ) * Complex.I) =
          (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
      rw [Complex.exp_ofReal_mul_I]
      rw [Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    have hposexp :
        Complex.exp ((x : ℂ) * Complex.I) =
          (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I :=
      Complex.exp_ofReal_mul_I x
    rw [hqinv]
    dsimp [q]
    rw [hnegexp, hposexp]
    push_cast
    ring
  have hceq := complex_tsum_eq_cg q hqnorm hslit
  have hsum := complex_summable q hqnorm.le
  calc
    (∑' n : ℕ,
      (-1 : ℝ) ^ (n + 2) *
        Real.cos (((n + 2 : ℕ) : ℝ) * x) /
          ((((n + 2 : ℕ) : ℝ) ^ 2) - 1)) =
        ∑' n : ℕ,
          (q ^ (n + 2) /
            ((((n + 2 : ℕ) : ℂ) ^ 2) - 1)).re := by
      apply tsum_congr
      intro n
      exact (complex_term_re x n).symm
    _ = (∑' n : ℕ,
          q ^ (n + 2) /
            ((((n + 2 : ℕ) : ℂ) ^ 2) - 1)).re :=
      (Complex.re_tsum hsum).symm
    _ = (cg q).re := congrArg Complex.re hceq
    _ = (1 / 2 : ℝ) * (1 - Real.cos x / 2) -
        x / 2 * Real.sin x := by
      have hprodre :
          ((q⁻¹ - q) * Complex.log (1 - q)).re =
            -x * Real.sin x := by
        rw [hqdiff, hlog]
        simp [Complex.mul_re, Complex.sin_ofReal_re]
        ring
      have hqdivre : (q / (2 : ℂ)).re = -Real.cos x / 2 := by
        rw [Complex.div_re]
        simp [q, Complex.normSq_apply]
        ring
      have hhalf (z : ℂ) :
          (((1 / 2 : ℂ) * z).re) = (1 / 2 : ℝ) * z.re := by
        rw [Complex.mul_re]
        norm_num [Complex.div_re, Complex.normSq_apply]
      unfold cg
      rw [hhalf]
      simp only [Complex.add_re, Complex.one_re]
      rw [hprodre, hqdivre]
      ring

private theorem reciprocal_quadratic_hasSum :
    HasSum
      (fun n : ℕ =>
        (1 : ℝ) / ((((n + 2 : ℕ) : ℝ) ^ 2) - 1))
      (3 / 4 : ℝ) := by
  let f : ℕ → ℝ := fun n =>
    (1 : ℝ) / ((((n + 2 : ℕ) : ℝ) ^ 2) - 1)
  have hp :
      Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [Function.comp_def] using
      ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).comp_injective
        Nat.succ_injective
  have hf : Summable f := by
    refine hp.of_norm_bounded ?_
    intro n
    have hden :
        ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) =
          ((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ) := by
      push_cast
      ring
    have hpos :
        0 < ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) := by
      rw [hden]
      positivity
    dsimp [f]
    rw [abs_of_pos (div_pos one_pos hpos), hden]
    gcongr
    push_cast
    nlinarith
  have hpf (n : ℕ) :
      f n =
        (1 / 2 : ℝ) *
          (1 / ((n + 1 : ℕ) : ℝ) -
            1 / ((n + 3 : ℕ) : ℝ)) := by
    dsimp [f]
    have h1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have h3 : (((n + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hden :
        ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) =
          ((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hden]
    field_simp
    push_cast
    ring
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N, f n) =
        (3 / 4 : ℝ) -
          (1 / 2 : ℝ) *
            (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 2)) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, hpf]
        push_cast
        field_simp
        ring
  refine (hasSum_iff_tendsto_nat_of_summable_norm hf.norm).2 ?_
  simp_rw [hsum]
  have h1 :
      Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1))
        atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 :
      Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 2))
        atTop (nhds 0) := by
    convert h1.comp (Filter.tendsto_add_atTop_nat 1) using 1
    funext N
    simp [Function.comp_def]
    ring
  have hc34 :
      Tendsto (fun _ : ℕ => (3 / 4 : ℝ)) atTop (nhds (3 / 4 : ℝ)) :=
    tendsto_const_nhds
  have hc12 :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  simpa using hc34.sub (hc12.mul (h1.add h2))

private theorem real_tsum_endpoint (x : ℝ)
    (hx : x = -Real.pi ∨ x = Real.pi) :
    (∑' n : ℕ,
      (-1 : ℝ) ^ (n + 2) *
        Real.cos (((n + 2 : ℕ) : ℝ) * x) /
          ((((n + 2 : ℕ) : ℝ) ^ 2) - 1)) =
      (1 / 2 : ℝ) * (1 - Real.cos x / 2) -
        x / 2 * Real.sin x := by
  have hterm (n : ℕ) :
      (-1 : ℝ) ^ (n + 2) *
          Real.cos (((n + 2 : ℕ) : ℝ) * x) /
            ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) =
        (1 : ℝ) / ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) := by
    rcases hx with rfl | rfl
    · rw [mul_neg, Real.cos_neg, Real.cos_nat_mul_pi]
      rw [← pow_add]
      simp
    · rw [Real.cos_nat_mul_pi]
      rw [← pow_add]
      simp
  calc
    (∑' n : ℕ,
      (-1 : ℝ) ^ (n + 2) *
        Real.cos (((n + 2 : ℕ) : ℝ) * x) /
          ((((n + 2 : ℕ) : ℝ) ^ 2) - 1)) =
        ∑' n : ℕ,
          (1 : ℝ) / ((((n + 2 : ℕ) : ℝ) ^ 2) - 1) :=
      tsum_congr hterm
    _ = 3 / 4 := reciprocal_quadratic_hasSum.tsum_eq
    _ = (1 / 2 : ℝ) * (1 - Real.cos x / 2) -
        x / 2 * Real.sin x := by
      rcases hx with rfl | rfl <;>
        simp [Real.cos_neg, Real.sin_neg] <;>
        ring

theorem gap9 (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    targetSeries x =
      (1 / 2 : ℝ) * (1 - Real.cos x / 2) - x / 2 * Real.sin x := by
  unfold targetSeries
  by_cases hm : x = -Real.pi
  · exact real_tsum_endpoint x (Or.inl hm)
  by_cases hp : x = Real.pi
  · exact real_tsum_endpoint x (Or.inr hp)
  exact real_tsum_interior x
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hm), lt_of_le_of_ne hx.2 hp⟩

end

end ProofGap.Exercise3023
