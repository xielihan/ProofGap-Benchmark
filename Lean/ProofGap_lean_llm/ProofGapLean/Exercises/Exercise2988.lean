import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2988

noncomputable section

open Filter
open scoped BigOperators

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * (n + 1 : ℝ))

def differenceTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) *
    (1 / (n : ℝ) - 1 / (n + 1 : ℝ))

def seriesSum : ℝ :=
  ∑' k : ℕ, term (k + 1)

def differenceSeries : ℝ :=
  ∑' k : ℕ, differenceTerm (k + 1)

def alternatingHarmonicPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (n + 1) / (n : ℝ)

def derivedPartial (N : ℕ) : ℝ :=
  2 * alternatingHarmonicPartial N +
    (-1 : ℝ) ^ (N + 2) / (N + 1 : ℝ) - 1

private theorem term_eq_differenceTerm (n : ℕ) (hn : 0 < n) :
    term n = differenceTerm n := by
  unfold term differenceTerm
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn0, hn1]
  <;> ring

private theorem alternatingHarmonicPartial_succ (N : ℕ) :
    alternatingHarmonicPartial (N + 1) =
      alternatingHarmonicPartial N +
        (-1 : ℝ) ^ (N + 2) / (N + 1 : ℝ) := by
  unfold alternatingHarmonicPartial
  have hIcc :
      Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext n
    simp
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  push_cast
  rw [show N + 1 + 1 = N + 2 by omega]
  ring

private theorem derivedPartial_succ (N : ℕ) :
    derivedPartial (N + 1) =
      derivedPartial N + differenceTerm (N + 1) := by
  rw [derivedPartial, derivedPartial, alternatingHarmonicPartial_succ]
  unfold differenceTerm
  push_cast
  rw [show N + 3 = (N + 2) + 1 by omega, pow_succ]
  ring

private theorem derivedPartial_eq_sum_range (N : ℕ) :
    derivedPartial N =
      ∑ k ∈ Finset.range N, differenceTerm (k + 1) := by
  induction N with
  | zero =>
      simp [derivedPartial, alternatingHarmonicPartial]
  | succ N ih =>
      rw [derivedPartial_succ, Finset.sum_range_succ, ih]

private theorem shiftedTerm_summable :
    Summable (fun k : ℕ => term (k + 1)) := by
  have hp : Summable (fun k : ℕ => 1 / ((((k + 1 : ℕ) : ℝ)) ^ 2)) := by
    simpa using
      ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2)))
  refine hp.of_norm_bounded ?_
  intro k
  rw [term, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)),
    abs_of_pos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  push_cast
  nlinarith

private theorem alternatingHarmonicPartial_eq_sum_range (N : ℕ) :
    alternatingHarmonicPartial N =
      ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k / (k + 1 : ℝ) := by
  induction N with
  | zero =>
      simp [alternatingHarmonicPartial]
  | succ N ih =>
      rw [alternatingHarmonicPartial_succ, Finset.sum_range_succ, ih]
      push_cast
      simp [pow_add]

private theorem tendsto_alternatingHarmonic_sum_range :
    Tendsto
      (fun N : ℕ =>
        ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k / (k + 1 : ℝ))
      atTop (nhds (Real.log 2)) := by
  obtain ⟨l, hl⟩ :
      ∃ l : ℝ,
        Tendsto
          (fun N : ℕ =>
            ∑ k ∈ Finset.range N,
              (-1 : ℝ) ^ k * (1 / (k + 1 : ℝ)))
          atTop (nhds l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · exact antitone_iff_forall_lt.mpr fun _ _ _ => by gcongr
    · have hden :
          Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop := by
        apply tendsto_atTop_add_const_right
        exact tendsto_natCast_atTop_atTop
      simpa only [one_div] using hden.inv_tendsto_atTop
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hleft : nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds 1 :=
    tendsto_nhdsWithin_of_tendsto_nhds fun _ hx => hx
  replace hab := hab.mul hleft
  rw [mul_one] at hab
  replace hab :
      Tendsto (fun x : ℝ => Real.log (1 + x))
        (nhdsWithin 1 (Set.Iio 1)) (nhds l) := by
    apply hab.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx hxlt
    have hxpos : 0 < x := by
      rw [Real.dist_eq, abs_sub_lt_iff] at hx
      linarith
    have hxabs : |-x| < 1 := by
      rw [abs_neg, abs_of_pos hxpos]
      exact hxlt
    have hs :
        HasSum
          (fun n : ℕ =>
            (((-1 : ℝ) ^ n * (1 / (n + 1 : ℝ))) * x ^ n) * x)
          (Real.log (1 + x)) := by
      convert (Real.hasSum_pow_div_log_of_abs_lt_one hxabs).neg using 1
      · funext n
        rw [pow_succ (-x) n, neg_pow x n]
        ring
      · congr 1 <;> ring
    rw [← hs.tsum_eq, ← tsum_mul_right]
  have hlog :
      Tendsto (fun x : ℝ => Real.log (1 + x))
        (nhdsWithin 1 (Set.Iio 1))
        (nhds (Real.log 2)) := by
    have harg :
        Tendsto (fun x : ℝ => 1 + x) (nhds (1 : ℝ)) (nhds (2 : ℝ)) := by
      convert
        (continuousAt_const.add continuousAt_id :
          ContinuousAt (fun x : ℝ => 1 + x) 1).tendsto using 1 <;>
        norm_num [Pi.add_apply]
    exact
      ((Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp harg).mono_left
        hleft
  have hlimit : l = Real.log 2 := tendsto_nhds_unique hab hlog
  simpa [div_eq_mul_inv, hlimit] using hl

theorem gap1 :
    seriesSum = differenceSeries := by
  unfold seriesSum differenceSeries
  apply tsum_congr
  intro k
  exact term_eq_differenceTerm (k + 1) (by omega)

theorem gap2 :
    Tendsto derivedPartial atTop (nhds seriesSum) := by
  have hsum :=
    shiftedTerm_summable.hasSum.tendsto_sum_nat
  apply hsum.congr'
  filter_upwards [] with N
  rw [derivedPartial_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  exact term_eq_differenceTerm (k + 1) (by omega)

theorem gap3 :
    Tendsto derivedPartial atTop (nhds (2 * Real.log 2 - 1)) := by
  have hA :
      Tendsto alternatingHarmonicPartial atTop (nhds (Real.log 2)) := by
    apply tendsto_alternatingHarmonic_sum_range.congr'
    filter_upwards [] with N
    exact (alternatingHarmonicPartial_eq_sum_range N).symm
  have hinv :
      Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (nhds 0) := by
    have hden :
        Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    simpa only [one_div] using hden.inv_tendsto_atTop
  have hcorrection :
      Tendsto (fun N : ℕ => (-1 : ℝ) ^ (N + 2) / (N + 1 : ℝ))
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    convert hinv using 1
    funext N
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
  convert ((tendsto_const_nhds.mul hA).add hcorrection).sub tendsto_const_nhds using 1 <;>
    ring

theorem gap4 :
    seriesSum = 2 * Real.log 2 - 1 := by
  exact tendsto_nhds_unique gap2 gap3

end

end ProofGap.Exercise2988
