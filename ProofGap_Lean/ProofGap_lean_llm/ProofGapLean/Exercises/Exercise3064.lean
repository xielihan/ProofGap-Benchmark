import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3064

noncomputable section

open Filter
open scoped BigOperators Topology

def exponent (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (n : ℝ)

def factor (a : ℝ) (n : ℕ) : ℝ :=
  Real.rpow a (exponent n)

def partialProduct (a : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, factor a i

def alternatingHarmonicPartial (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (i + 1) / (i : ℝ)

def closedForm (a : ℝ) (n : ℕ) : ℝ :=
  Real.rpow a (-alternatingHarmonicPartial n)

def ConvergentProduct (a : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (partialProduct a) atTop (𝓝 L)

def HasProduct (a L : ℝ) : Prop :=
  Tendsto (partialProduct a) atTop (𝓝 L)

private theorem alternatingHarmonicPartial_succ (n : ℕ) :
    alternatingHarmonicPartial (n + 1) =
      alternatingHarmonicPartial n +
        (-1 : ℝ) ^ (n + 2) / (n + 1 : ℝ) := by
  unfold alternatingHarmonicPartial
  have hIcc :
      Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext i
    simp
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  push_cast
  rw [show n + 1 + 1 = n + 2 by omega]
  ring

private theorem alternatingHarmonicPartial_eq_sum_range (n : ℕ) :
    alternatingHarmonicPartial n =
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (i + 1 : ℝ) := by
  induction n with
  | zero =>
      simp [alternatingHarmonicPartial]
  | succ n ih =>
      rw [alternatingHarmonicPartial_succ, Finset.sum_range_succ, ih]
      push_cast
      simp [pow_add]

private theorem tendsto_alternatingHarmonic_sum_range :
    Tendsto
      (fun n : ℕ =>
        ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (i + 1 : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  obtain ⟨l, hl⟩ :
      ∃ l : ℝ,
        Tendsto
          (fun n : ℕ =>
            ∑ i ∈ Finset.range n,
              (-1 : ℝ) ^ i * (1 / (i + 1 : ℝ)))
          atTop (𝓝 l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · exact antitone_iff_forall_lt.mpr fun _ _ _ => by gcongr
    · have hden :
          Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop := by
        apply tendsto_atTop_add_const_right
        exact tendsto_natCast_atTop_atTop
      simpa only [one_div] using hden.inv_tendsto_atTop
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hleft : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 :=
    tendsto_nhdsWithin_of_tendsto_nhds fun _ hx => hx
  replace hab := hab.mul hleft
  rw [mul_one] at hab
  replace hab :
      Tendsto (fun x : ℝ => Real.log (1 + x))
        (𝓝[<] 1) (𝓝 l) := by
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
            (((-1 : ℝ) ^ n * (1 / (n + 1 : ℝ)) * x ^ n) * x))
          (Real.log (1 + x)) := by
      convert (Real.hasSum_pow_div_log_of_abs_lt_one hxabs).neg using 1
      · funext n
        rw [pow_succ (-x) n, neg_pow x n]
        ring
      · congr 1 <;> ring
    rw [← hs.tsum_eq, ← tsum_mul_right]
  have hlog :
      Tendsto (fun x : ℝ => Real.log (1 + x))
        (𝓝[<] 1) (𝓝 (Real.log 2)) := by
    have harg :
        Tendsto (fun x : ℝ => 1 + x) (𝓝 (1 : ℝ)) (𝓝 (2 : ℝ)) := by
      convert
        (continuousAt_const.add continuousAt_id :
          ContinuousAt (fun x : ℝ => 1 + x) 1).tendsto using 1 <;>
        norm_num [Pi.add_apply]
    exact
      ((Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp harg).mono_left
        hleft
  have hlimit : l = Real.log 2 := tendsto_nhds_unique hab hlog
  simpa [div_eq_mul_inv, hlimit] using hl

private theorem tendsto_alternatingHarmonicPartial :
    Tendsto alternatingHarmonicPartial atTop (𝓝 (Real.log 2)) := by
  apply tendsto_alternatingHarmonic_sum_range.congr'
  filter_upwards [] with n
  exact (alternatingHarmonicPartial_eq_sum_range n).symm

/-- Exercise 3064, gap 1; use an exact product and real powers. -/
theorem gap1 (a : ℝ) (ha : 0 < a) (P : ℕ → ℝ)
    (hP : ∀ n, P n = partialProduct a n) :
    ∀ n, P n = partialProduct a n := by
  exact hP

/-- Exercise 3064, gap 2; replace both ellipses by finite operators. -/
theorem gap2 (a : ℝ) (ha : 0 < a) :
    ∀ n, partialProduct a n = closedForm a n := by
  intro n
  rw [partialProduct, closedForm]
  simp only [factor]
  change (∏ i ∈ Finset.Icc 1 n, a ^ exponent i) =
    a ^ (-alternatingHarmonicPartial n)
  rw [← Real.rpow_sum_of_pos ha]
  congr 1
  rw [alternatingHarmonicPartial, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [exponent, pow_succ]
  ring

/-- Exercise 3064, gap 3. -/
theorem gap3 (a : ℝ) (ha : 0 < a) (P : ℕ → ℝ)
    (hP : ∀ n, P n = partialProduct a n) :
    ∀ n, P n = closedForm a n := by
  intro n
  rw [hP n, gap2 a ha n]

/-- Exercise 3064, gap 4; interpret the variable exponent by `Real.rpow`. -/
theorem gap4 (a : ℝ) (ha : 0 < a) (P : ℕ → ℝ)
    (hP : ∀ n, P n = partialProduct a n) :
    Tendsto P atTop (𝓝 (Real.rpow a (-Real.log 2))) := by
  have hclosed :
      Tendsto (closedForm a) atTop
        (𝓝 (Real.rpow a (-Real.log 2))) := by
    unfold closedForm
    simpa [Function.comp_def] using
      (Real.continuous_const_rpow ha.ne').continuousAt.tendsto.comp
        tendsto_alternatingHarmonicPartial.neg
  apply hclosed.congr'
  filter_upwards [] with n
  exact (gap3 a ha P hP n).symm

/-- Exercise 3064, gap 5. -/
theorem gap5 (a : ℝ) (ha : 0 < a) :
    ConvergentProduct a := by
  refine ⟨Real.rpow a (-Real.log 2), ?_⟩
  exact gap4 a ha (partialProduct a) (fun _ => rfl)

/-- Exercise 3064, gap 6; interpret the value by `Real.rpow`. -/
theorem gap6 (a : ℝ) (ha : 0 < a) :
    HasProduct a (Real.rpow a (-Real.log 2)) := by
  exact gap4 a ha (partialProduct a) (fun _ => rfl)

end

end ProofGap.Exercise3064
