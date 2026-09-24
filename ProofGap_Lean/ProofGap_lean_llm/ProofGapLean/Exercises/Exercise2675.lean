import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2675

noncomputable section

open Filter

def magnitude (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n p

def term (p : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) * magnitude p n

def ConditionallySummable (p : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) ∧
    ¬ Summable (fun n : ℕ => magnitude p (n + 1))

private theorem seriesConverges_tendsto_zero {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) :
    Tendsto f atTop (nhds 0) := by
  rcases hf with ⟨s, hs⟩
  have hsum :
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (nhds s) := by
    unfold HasSum at hs
    rw [SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff] at hs
    simpa [Function.comp_def] using hs
  have hsumSucc := hsum.comp (tendsto_add_atTop_nat 1)
  have hdiff := hsumSucc.sub hsum
  simpa [Finset.sum_range_succ] using hdiff

theorem gap1 :
    ∀ p : ℝ, p < 0 →
      Tendsto (fun n : ℕ => magnitude p (n + 1)) atTop atTop := by
  intro p hp
  have hbase :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow :=
    (tendsto_rpow_atTop (neg_pos.mpr hp)).comp hbase
  convert hpow using 1
  funext n
  simp only [Function.comp_apply, magnitude, one_div]
  exact (Real.rpow_neg (by positivity) p).symm

theorem gap2 :
    ∀ p : ℝ, p < 0 →
      ¬ ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) := by
  intro p hp hsum
  have hzero :
      Tendsto (fun n : ℕ => |term p (n + 1)|) atTop (nhds 0) := by
    simpa using (seriesConverges_tendsto_zero hsum).abs
  have hmagzero :
      Tendsto (fun n : ℕ => magnitude p (n + 1)) atTop (nhds 0) := by
    convert hzero using 1
    funext n
    unfold term
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by
        unfold magnitude
        exact div_nonneg zero_le_one
          (Real.rpow_nonneg (by positivity) p))]
  exact not_tendsto_nhds_of_tendsto_atTop (gap1 p hp) 0 hmagzero

theorem gap3 :
    ∀ p : ℝ, p = 0 → ∀ n : ℕ, 1 ≤ n → magnitude p n = 1 := by
  intro p hp n hn
  subst p
  simp [magnitude]

theorem gap4 :
    ∀ p : ℝ, p = 0 →
      ¬ ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) := by
  intro p hp hsum
  subst p
  have hzero :
      Tendsto (fun n : ℕ => |term 0 (n + 1)|) atTop (nhds 0) := by
    simpa using (seriesConverges_tendsto_zero hsum).abs
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    convert hzero using 1
    funext n
    simp [term, magnitude]
  have hEq : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hone
  norm_num at hEq

theorem gap5 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      Tendsto (fun n : ℕ => magnitude p (n + 1)) atTop (nhds 0) := by
  intro p hp hp1
  have hbase :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow :=
    (tendsto_rpow_neg_atTop hp).comp hbase
  convert hpow using 1
  funext n
  simp only [Function.comp_apply, magnitude, one_div]
  exact (Real.rpow_neg (by positivity) p).symm

theorem gap6 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      Antitone (fun n : ℕ => magnitude p (n + 1)) := by
  intro p hp hp1 m n hmn
  have hle :
      (((m + 1 : ℕ) : ℝ) ^ (-p)) ≥ (((n + 1 : ℕ) : ℝ) ^ (-p)) :=
    Real.rpow_le_rpow_of_nonpos
      (show 0 < ((m + 1 : ℕ) : ℝ) by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
      (show -p ≤ 0 by linarith)
  unfold magnitude
  simp only [one_div]
  rw [Real.rpow_neg (by positivity) p,
    Real.rpow_neg (by positivity) p] at hle
  exact hle

theorem gap7 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) := by
  intro p hp hp1
  obtain ⟨l, hl⟩ :=
    (gap6 p hp hp1).tendsto_alternating_series_of_tendsto_zero
      (gap5 p hp hp1)
  unfold ProofGap.SeriesConverges
  refine ⟨l, ?_⟩
  unfold HasSum
  rw [SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def, term] using hl

theorem gap8 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ¬ Summable (fun n : ℕ => magnitude p (n + 1)) := by
  intro p hp hp1 hshift
  have hshift' :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ p)) := by
    simpa [magnitude] using hshift
  have hfull :
      Summable (fun n : ℕ => 1 / ((n : ℝ) ^ p)) :=
    (_root_.summable_nat_add_iff 1).mp hshift'
  have hp' : 1 < p :=
    Real.summable_one_div_nat_rpow.mp hfull
  linarith

theorem gap9 :
    ∀ p : ℝ, 0 < p → p ≤ 1 → ConditionallySummable p := by
  intro p hp hp1
  exact ⟨gap7 p hp hp1, gap8 p hp hp1⟩

theorem gap10 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => magnitude p (n + 1)) := by
  intro p hp
  have hfull :
      Summable (fun n : ℕ => 1 / ((n : ℝ) ^ p)) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hshift :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ p)) :=
    (_root_.summable_nat_add_iff 1).mpr hfull
  simpa [magnitude] using hshift

theorem gap11 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => |term p (n + 1)|) := by
  intro p hp
  refine (gap10 p hp).congr (fun n => ?_)
  unfold term
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by
      unfold magnitude
      exact div_nonneg zero_le_one
        (Real.rpow_nonneg (by positivity) p))]

end

end ProofGap.Exercise2675
