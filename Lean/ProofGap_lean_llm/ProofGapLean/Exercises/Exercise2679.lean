import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2679

noncomputable section

open Filter

def IsNegativeInteger (x : ℝ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ x = -(n : ℝ)

def magnitude (x : ℝ) (n : ℕ) : ℝ :=
  1 / (x + n)

def term (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (x + n)

def ConditionallySummable (x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term x (n + 1)) ∧
    ¬ ProofGap.SeriesConverges (fun n : ℕ => |term x (n + 1)|)

theorem gap1 :
    ∀ x : ℝ, IsNegativeInteger x →
      ∃ n : ℕ, 1 ≤ n ∧ x + n = 0 := by
  rintro x ⟨n, hn, rfl⟩
  exact ⟨n, hn, by simp⟩

theorem gap2 :
    ∀ x : ℝ, ¬ IsNegativeInteger x →
      ∃ N : ℕ, Antitone (fun n : ℕ => magnitude x (n + N)) := by
  intro x hx
  obtain ⟨N, hN⟩ := exists_nat_gt (-x)
  refine ⟨N, ?_⟩
  intro i j hij
  unfold magnitude
  apply one_div_le_one_div_of_le
  · push_cast
    nlinarith
  · have hc : ((i + N : ℕ) : ℝ) ≤ ((j + N : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hij N
    linarith

theorem gap3 :
    ∀ x : ℝ, ¬ IsNegativeInteger x →
      Tendsto (fun n : ℕ => magnitude x (n + 1)) atTop (nhds 0) := by
  intro x hx
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + (x + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ (x + 1) tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp htop
  simpa [magnitude, one_div, add_comm, add_left_comm, add_assoc] using hinv

theorem gap4 :
    ∀ x : ℝ, ¬ IsNegativeInteger x →
      ProofGap.SeriesConverges (fun n : ℕ => term x (n + 1)) := by
  intro x hx
  obtain ⟨K, hK⟩ := exists_nat_gt (-x)
  let coeff : ℕ → ℝ := fun n => magnitude x (n + K + 1)
  have hcoeffAnti : Antitone coeff := by
    intro i j hij
    dsimp [coeff, magnitude]
    apply one_div_le_one_div_of_le
    · push_cast
      nlinarith
    · have hc : ((i + K + 1 : ℕ) : ℝ) ≤ ((j + K + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hij (K + 1)
      linarith
  have hcoeffZero : Tendsto coeff atTop (nhds 0) := by
    have hbase := gap3 x hx
    simpa [coeff, Nat.add_assoc] using
      hbase.comp (tendsto_add_atTop_nat K)
  rcases hcoeffAnti.tendsto_alternating_series_of_tendsto_zero hcoeffZero with
    ⟨L, hL⟩
  let sign : ℝ := (-1 : ℝ) ^ (K + 1)
  have htermEq (i : ℕ) :
      term x (i + K + 1) = sign * ((-1 : ℝ) ^ i * coeff i) := by
    dsimp [term, sign, coeff, magnitude]
    rw [show i + K + 1 = i + (K + 1) by omega, pow_add]
    ring
  have htailFun :
      (fun n : ℕ => ∑ i ∈ Finset.range n, term x (i + K + 1)) =
        fun n : ℕ => sign * ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * coeff i := by
    funext n
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => htermEq i
  have htailLim : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, term x (i + K + 1))
      atTop (nhds (sign * L)) := by
    rw [htailFun]
    exact hL.const_mul sign
  let g : ℕ → ℝ := fun n => term x (n + 1)
  let partialS : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, g i
  have hshiftFun :
      (fun n : ℕ => partialS (n + K)) =
        fun n : ℕ => partialS K +
          ∑ i ∈ Finset.range n, term x (i + K + 1) := by
    funext n
    simpa [partialS, g, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Finset.sum_range_add g K n
  have hshiftLim : Tendsto (fun n : ℕ => partialS (n + K)) atTop
      (nhds (partialS K + sign * L)) := by
    rw [hshiftFun]
    exact tendsto_const_nhds.add htailLim
  have hfullLim : Tendsto partialS atTop (nhds (partialS K + sign * L)) :=
    (tendsto_add_atTop_iff_nat K).1 hshiftLim
  change Summable g (SummationFilter.conditional ℕ)
  refine ⟨partialS K + sign * L, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff, Function.comp_def]
  exact hfullLim

theorem gap5 :
    ∀ x : ℝ, ¬ IsNegativeInteger x →
      ¬ Summable (fun n : ℕ => magnitude x (n + 1)) := by
  intro x hx hsum
  have hnorm := hsum.norm
  have hpseries : Summable
      (fun n : ℕ => 1 / |(n : ℝ) + (x + 1)| ^ (1 : ℝ)) := by
    convert hnorm using 1 with n
    simp [magnitude, Real.norm_eq_abs, Real.rpow_one, abs_div,
      add_comm, add_left_comm, add_assoc]
  have hfalse := (Real.summable_one_div_nat_add_rpow (x + 1) 1).1 hpseries
  norm_num at hfalse

theorem gap6 :
    ∀ x : ℝ, ¬ IsNegativeInteger x → ConditionallySummable x := by
  intro x hx
  refine ⟨gap4 x hx, ?_⟩
  intro habs
  change Summable (fun n : ℕ => |term x (n + 1)|)
    (SummationFilter.conditional ℕ) at habs
  rcases habs with ⟨s, hs⟩
  have hpartial : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, |term x (i + 1)|)
      atTop (nhds s) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff, Function.comp_def] at hs
    exact hs
  rcases (bddAbove_def.1 hpartial.bddAbove_range) with ⟨C, hC⟩
  have huncond : Summable (fun n : ℕ => |term x (n + 1)|) :=
    summable_of_sum_range_le (fun n => abs_nonneg _) fun n =>
      hC _ ⟨n, rfl⟩
  have hmagNorm : Summable
      (fun n : ℕ => ‖magnitude x (n + 1)‖) := by
    refine huncond.congr ?_
    intro n
    simp [term, magnitude, Real.norm_eq_abs, abs_div]
  have hmag : Summable (fun n : ℕ => magnitude x (n + 1)) :=
    summable_norm_iff.mp hmagNorm
  exact gap5 x hx hmag

end

end ProofGap.Exercise2679
