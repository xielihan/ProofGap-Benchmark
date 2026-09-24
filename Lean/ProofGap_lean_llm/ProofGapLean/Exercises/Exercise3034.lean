import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ProofGap.Exercise3034

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def logSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, -(x ^ (n + 1) / ((n + 1 : ℕ) : ℝ))

def positiveLogSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)

def finiteLogPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  -∑ k ∈ Finset.Icc 1 n, x ^ k / (k : ℝ)

def integratedPartial (τ : ℝ) (n : ℕ) : ℝ :=
  -∑ k ∈ Finset.Icc 1 n, τ ^ (k + 1) / ((k : ℝ) * (k + 1 : ℝ))

def remainder (n : ℕ) (τ : ℝ) : ℝ :=
  (∫ x in 0..τ, Real.log (1 - x)) -
    ∫ x in 0..τ, finiteLogPolynomial n x

private theorem finiteLogPolynomial_eq_range (n : ℕ) (x : ℝ) :
    finiteLogPolynomial n x =
      -∑ k ∈ Finset.range n, x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold finiteLogPolynomial
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

private theorem log_sub_finite_neg (n : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (1 - x) - finiteLogPolynomial n x < 0 := by
  let f : ℕ → ℝ := fun k => x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
  have habs : |x| < 1 := by simpa [abs_of_pos hx0] using hx1
  have hs : HasSum f (-Real.log (1 - x)) := by
    simpa [f, Nat.cast_add, Nat.cast_one] using
      Real.hasSum_pow_div_log_of_abs_lt_one habs
  have htail : Summable (fun k => f (k + n)) := by
    exact ((summable_nat_add_iff n).mpr hs.summable)
  have htailpos : 0 < ∑' k : ℕ, f (k + n) := by
    exact htail.tsum_pos (fun k => by
      dsimp [f]
      positivity) 0 (by
        dsimp [f]
        positivity)
  have hsplit := hs.summable.sum_add_tsum_nat_add n
  have htotal := hs.tsum_eq
  rw [finiteLogPolynomial_eq_range, sub_neg_eq_add]
  dsimp [f] at hsplit htailpos htotal
  linarith

private theorem integral_log_one_sub :
    (∫ x in (0 : ℝ)..1, Real.log (1 - x)) = -1 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => Real.log x) 1]
  norm_num [integral_log]

private theorem integral_finiteLogPolynomial (n : ℕ) (τ : ℝ) :
    (∫ x in (0 : ℝ)..τ, finiteLogPolynomial n x) =
      integratedPartial τ n := by
  unfold finiteLogPolynomial integratedPartial
  rw [intervalIntegral.integral_neg]
  congr 1
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_div]
    rw [integral_pow]
    have hk1 : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by norm_num
    rw [hk1]
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    field_simp
    ring
  · intro k hk
    show IntervalIntegrable (fun x : ℝ => x ^ k / (k : ℝ))
      MeasureTheory.volume 0 τ
    exact (show Continuous (fun x : ℝ => x ^ k / (k : ℝ)) by
      fun_prop).intervalIntegrable (μ := MeasureTheory.volume) 0 τ

private theorem integratedPartial_one_eq (n : ℕ) :
    integratedPartial 1 n =
      -(1 : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by
  unfold integratedPartial
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp only [one_pow, neg_add_rev]
      simp only [one_pow] at ih
      rw [ih]
      push_cast
      field_simp
      ring

private theorem remainder_one_eq (n : ℕ) :
    remainder n 1 = -(1 / ((n + 1 : ℕ) : ℝ)) := by
  unfold remainder
  rw [integral_log_one_sub, integral_finiteLogPolynomial,
    integratedPartial_one_eq]
  ring

private theorem finiteLogPolynomial_continuous (n : ℕ) :
    Continuous (finiteLogPolynomial n) := by
  unfold finiteLogPolynomial
  fun_prop

private theorem log_one_sub_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log (1 - x))
      MeasureTheory.volume a b := by
  have h :=
    (intervalIntegral.intervalIntegrable_log'
      (a := 1 - b) (b := 1 - a)).comp_sub_left 1
  simpa only [sub_sub_cancel] using h.symm

private theorem remainder_eq_integral (n : ℕ) (τ : ℝ) :
    remainder n τ =
      ∫ x in (0 : ℝ)..τ,
        Real.log (1 - x) - finiteLogPolynomial n x := by
  unfold remainder
  rw [intervalIntegral.integral_sub
    (log_one_sub_intervalIntegrable 0 τ)
    ((finiteLogPolynomial_continuous n).intervalIntegrable
      (μ := MeasureTheory.volume) 0 τ)]

private theorem residual_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => Real.log (1 - x) - finiteLogPolynomial n x)
      MeasureTheory.volume a b :=
  (log_one_sub_intervalIntegrable a b).sub
    ((finiteLogPolynomial_continuous n).intervalIntegrable
      (μ := MeasureTheory.volume) a b)

private theorem residual_continuousOn (n : ℕ) {a b : ℝ}
    (hb : b < 1) :
    ContinuousOn
      (fun x : ℝ => Real.log (1 - x) - finiteLogPolynomial n x)
      (Set.Icc a b) := by
  apply ContinuousOn.sub
  · apply ContinuousOn.log
    · fun_prop
    · intro x hx
      linarith [hx.2]
  · exact (finiteLogPolynomial_continuous n).continuousOn

private theorem remainder_neg (n : ℕ) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    remainder n τ < 0 := by
  rw [remainder_eq_integral]
  have hcont := residual_continuousOn (a := 0) n hτ1
  have hlt :
      (∫ x in (0 : ℝ)..τ,
        Real.log (1 - x) - finiteLogPolynomial n x) <
        ∫ _x in (0 : ℝ)..τ, (0 : ℝ) := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hτ0 hcont continuousOn_const
    · intro x hx
      exact (log_sub_finite_neg n hx.1 (lt_of_le_of_lt hx.2 hτ1)).le
    · refine ⟨τ / 2, ⟨by linarith, by linarith⟩, ?_⟩
      exact log_sub_finite_neg n (by linarith) (by linarith)
  simpa using hlt

private theorem residual_tail_integral_neg (n : ℕ) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∫ x in τ..(1 : ℝ),
      Real.log (1 - x) - finiteLogPolynomial n x) < 0 := by
  let s : ℝ := (τ + 1) / 2
  have hτs : τ < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hs0 : 0 < s := hτ0.trans hτs
  have hleft :
      (∫ x in τ..s,
        Real.log (1 - x) - finiteLogPolynomial n x) < 0 := by
    have hlt :
        (∫ x in τ..s,
          Real.log (1 - x) - finiteLogPolynomial n x) <
          ∫ _x in τ..s, (0 : ℝ) := by
      apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        hτs (residual_continuousOn (a := τ) n hs1) continuousOn_const
      · intro x hx
        exact (log_sub_finite_neg n (hτ0.trans hx.1)
          (lt_of_le_of_lt hx.2 hs1)).le
      · refine ⟨(τ + s) / 2, ⟨by linarith, by linarith⟩, ?_⟩
        exact log_sub_finite_neg n (by linarith) (by linarith)
    simpa using hlt
  have hright :
      (∫ x in s..(1 : ℝ),
        Real.log (1 - x) - finiteLogPolynomial n x) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hs1.le]
    apply MeasureTheory.integral_nonpos_of_ae
    change ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioc s 1),
      Real.log (1 - x) - finiteLogPolynomial n x ≤ 0
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [MeasureTheory.volume.ae_ne (1 : ℝ)] with x hx hmem
    have hx1 : x < 1 := lt_of_le_of_ne hmem.2 hx
    exact (log_sub_finite_neg n (hs0.trans hmem.1) hx1).le
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (residual_intervalIntegrable n τ s)
      (residual_intervalIntegrable n s 1)
  linarith

private theorem remainder_lower (n : ℕ) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    -(1 / ((n + 1 : ℕ) : ℝ)) < remainder n τ := by
  rw [← remainder_one_eq n, remainder_eq_integral, remainder_eq_integral]
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (residual_intervalIntegrable n 0 τ)
      (residual_intervalIntegrable n τ 1)
  have htail := residual_tail_integral_neg n τ hτ0 hτ1
  linarith

private theorem reciprocal_hasSum :
    HasSum
      (fun n : ℕ =>
        (1 : ℝ) /
          (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)))
      1 := by
  let f : ℕ → ℝ := fun n =>
    (1 : ℝ) /
      (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))
  have hp :
      Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [Function.comp_def] using
      ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).comp_injective
        Nat.succ_injective
  have hf : Summable f := by
    refine hp.of_norm_bounded ?_
    intro n
    have hpos :
        0 < (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by positivity
    dsimp [f]
    rw [abs_of_pos (div_pos one_pos hpos)]
    gcongr
    push_cast
    nlinarith
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N, f n) =
        1 - 1 / ((N : ℝ) + 1) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [f]
        push_cast
        field_simp
        ring
  refine (hasSum_iff_tendsto_nat_of_summable_norm hf.norm).2 ?_
  simp_rw [hsum]
  simpa using
    (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1))
          atTop (𝓝 0)))

private theorem reciprocal_partial_sum (n : ℕ) :
    (∑ k ∈ Finset.range n,
      (1 : ℝ) /
        (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))) =
      1 - 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

private theorem reciprocal_tail_hasSum (n : ℕ) :
    HasSum
      (fun k : ℕ =>
        (1 : ℝ) /
          (((n + k + 1 : ℕ) : ℝ) *
            ((n + k + 2 : ℕ) : ℝ)))
      (1 / ((n + 1 : ℕ) : ℝ)) := by
  convert (hasSum_nat_add_iff' n).mpr reciprocal_hasSum using 1
  · funext k
    simp only [Nat.add_comm n k]
  · rw [reciprocal_partial_sum]
    ring

private theorem integral_power_term (n : ℕ) :
    (∫ x in (0 : ℝ)..1,
      x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) =
      1 /
        (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  rw [intervalIntegral.integral_div, integral_pow]
  norm_num
  field_simp
  ring

private theorem integral_log_reciprocal :
    (∫ x in (0 : ℝ)..1, Real.log (1 / (1 - x))) = 1 := by
  calc
    (∫ x in (0 : ℝ)..1, Real.log (1 / (1 - x))) =
        ∫ x in (0 : ℝ)..1, -Real.log (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change Real.log (1 / (1 - x)) = -Real.log (1 - x)
      rw [one_div, Real.log_inv]
    _ = -(∫ x in (0 : ℝ)..1, Real.log (1 - x)) := by
      rw [intervalIntegral.integral_neg]
    _ = 1 := by rw [integral_log_one_sub]; norm_num

private theorem logSeries_eq_log {x : ℝ} (hx : |x| < 1) :
    logSeries x = Real.log (1 - x) := by
  unfold logSeries
  have hs := (Real.hasSum_pow_div_log_of_abs_lt_one hx).neg
  simpa [Nat.cast_add, Nat.cast_one] using hs.tsum_eq

private theorem integral_logSeries :
    (∫ x in (0 : ℝ)..1, logSeries x) = -1 := by
  calc
    (∫ x in (0 : ℝ)..1, logSeries x) =
        ∫ x in (0 : ℝ)..1, Real.log (1 - x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.volume.ae_ne (1 : ℝ)] with x hx hmem
      rw [Set.uIoc_of_le zero_le_one] at hmem
      have hx0 : 0 < x := hmem.1
      have hx1 : x < 1 := lt_of_le_of_ne hmem.2 hx
      exact logSeries_eq_log (by simpa [abs_of_pos hx0] using hx1)
    _ = -1 := integral_log_one_sub

private theorem integratedPartial_tendsto_neg_one :
    Tendsto (integratedPartial 1) atTop (𝓝 (-1 : ℝ)) := by
  change Tendsto (fun n : ℕ => integratedPartial 1 n) atTop (𝓝 (-1 : ℝ))
  have hzero :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h :
      Tendsto (fun n : ℕ => (-1 : ℝ) + 1 / ((n : ℝ) + 1))
        atTop (𝓝 ((-1 : ℝ) + 0)) :=
    tendsto_const_nhds.add hzero
  simpa [integratedPartial_one_eq, Nat.cast_add, Nat.cast_one] using h

theorem gap1 :
    (∫ x in (0 : ℝ)..1, Real.log (1 / (1 - x))) =
      -(∫ x in (0 : ℝ)..1, Real.log (1 - x)) := by
  rw [integral_log_reciprocal, integral_log_one_sub]
  norm_num

theorem gap2 :
    -(∫ x in (0 : ℝ)..1, Real.log (1 - x)) =
      -(∫ x in (0 : ℝ)..1, logSeries x) := by
  rw [integral_log_one_sub, integral_logSeries]

theorem gap3 :
    (∫ x in (0 : ℝ)..1, Real.log (1 / (1 - x))) =
      -(∫ x in (0 : ℝ)..1, logSeries x) := by
  rw [integral_log_reciprocal, integral_logSeries]
  norm_num

theorem gap4 :
    (∫ x in (0 : ℝ)..1, Real.log (1 / (1 - x))) =
      ∑' n : ℕ,
        ∫ x in (0 : ℝ)..1, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  rw [integral_log_reciprocal]
  calc
    (1 : ℝ) =
        ∑' n : ℕ,
          1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) :=
      reciprocal_hasSum.tsum_eq.symm
    _ =
        ∑' n : ℕ,
          ∫ x in (0 : ℝ)..1, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
      apply tsum_congr
      intro n
      exact (integral_power_term n).symm

theorem gap5 :
    (∫ x in (0 : ℝ)..1, Real.log (1 / (1 - x))) =
      ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  rw [integral_log_reciprocal, reciprocal_hasSum.tsum_eq]

theorem gap6 :
    (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) = 1 := by
  exact reciprocal_hasSum.tsum_eq

theorem gap7 :
    (∫ x in (0 : ℝ)..1, Real.log (1 / (1 - x))) = 1 := by
  exact integral_log_reciprocal

theorem gap8 (n : ℕ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∫ x in (0 : ℝ)..τ, Real.log (1 - x)) =
      (∫ x in (0 : ℝ)..τ, finiteLogPolynomial n x) + remainder n τ := by
  unfold remainder
  ring

theorem gap9 (n : ℕ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    remainder n τ =
      ∫ x in (0 : ℝ)..τ,
        Real.log (1 - x) - finiteLogPolynomial n x := by
  exact remainder_eq_integral n τ

theorem gap10 (n : ℕ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    remainder n τ < 0 := by
  exact remainder_neg n τ hτ0 hτ1

theorem gap11 (n : ℕ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    -(1 / ((n + 1 : ℕ) : ℝ)) < remainder n τ := by
  exact remainder_lower n τ hτ0 hτ1

theorem gap12 (n : ℕ) :
    -(∑' k : ℕ,
      1 / (((n + k + 1 : ℕ) : ℝ) * ((n + k + 2 : ℕ) : ℝ))) =
      -(1 / ((n + 1 : ℕ) : ℝ)) := by
  rw [(reciprocal_tail_hasSum n).tsum_eq]

theorem gap13 (n : ℕ) : -(1 / ((n + 1 : ℕ) : ℝ)) < 0 := by
  have h : 0 < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  linarith

theorem gap14 (n : ℕ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    |(∫ x in (0 : ℝ)..τ, Real.log (1 - x)) - integratedPartial τ n| <
      1 / ((n + 1 : ℕ) : ℝ) := by
  rw [← integral_finiteLogPolynomial]
  change |remainder n τ| < 1 / ((n + 1 : ℕ) : ℝ)
  rw [abs_of_neg (remainder_neg n τ hτ0 hτ1)]
  linarith [remainder_lower n τ hτ0 hτ1]

theorem gap15 (n : ℕ) :
    |(∫ x in (0 : ℝ)..1, Real.log (1 - x)) - integratedPartial 1 n| ≤
      1 / ((n + 1 : ℕ) : ℝ) := by
  rw [← integral_finiteLogPolynomial]
  change |remainder n 1| ≤ 1 / ((n + 1 : ℕ) : ℝ)
  rw [remainder_one_eq]
  rw [abs_neg, abs_of_nonneg (by positivity)]

theorem gap16 :
    Tendsto (integratedPartial 1) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, Real.log (1 - x))) := by
  simpa [integral_log_one_sub] using integratedPartial_tendsto_neg_one

theorem gap17 :
    Tendsto (integratedPartial 1) atTop
      (𝓝 (∑' n : ℕ,
        -(1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))))) := by
  simpa only [reciprocal_hasSum.neg.tsum_eq] using
    integratedPartial_tendsto_neg_one

theorem gap18 :
    (∫ x in (0 : ℝ)..1, Real.log (1 - x)) =
      ∑' n : ℕ,
        -(1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) := by
  rw [integral_log_one_sub, reciprocal_hasSum.neg.tsum_eq]

theorem gap19 :
    (∫ x in (0 : ℝ)..1, logSeries x) =
      ∑' n : ℕ,
        ∫ x in (0 : ℝ)..1,
          -(x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
  calc
    (∫ x in (0 : ℝ)..1, logSeries x) = -1 := integral_logSeries
    _ =
        ∑' n : ℕ,
          -(1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) :=
      reciprocal_hasSum.neg.tsum_eq.symm
    _ =
        ∑' n : ℕ,
          ∫ x in (0 : ℝ)..1,
            -(x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
      apply tsum_congr
      intro n
      rw [intervalIntegral.integral_neg, integral_power_term]

end

end ProofGap.Exercise3034
