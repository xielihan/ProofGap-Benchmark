import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2683

noncomputable section

open Filter

def mainTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) /
    Real.rpow n (1 / 100 : ℝ)

def leadingTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / Real.rpow n (1 / 100 : ℝ)

def relativeError (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) / ((n : ℝ) + 1) - 1

def remainder (n : ℕ) : ℝ :=
  leadingTerm n * relativeError n

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧
    ¬ ProofGap.SeriesConverges (fun n => |f n|)

private theorem seriesConverges_of_tendsto_sum_range {f : ℕ → ℝ} {s : ℝ}
    (h : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (nhds s)) :
    ProofGap.SeriesConverges f := by
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_def]
  exact h

private theorem unconditional_of_seriesConverges_of_nonneg {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (h : ProofGap.SeriesConverges f) : Summable f := by
  rcases h with ⟨s, hs⟩
  refine ⟨s, (hasSum_iff_tendsto_nat_of_nonneg hf s).2 ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_def] at hs
  exact hs

private theorem seriesConverges_of_summable {f : ℕ → ℝ} (h : Summable f) :
    ProofGap.SeriesConverges f :=
  h.mono_filter (SummationFilter.conditional ℕ).le_atTop

theorem gap1 :
    (∀ n : ℕ, 1 ≤ n →
      mainTerm n = leadingTerm n * (1 + relativeError n)) ∧
    Asymptotics.IsBigO atTop relativeError
      (fun n : ℕ => 1 / (n : ℝ)) := by
  constructor
  · intro n hn
    simp only [mainTerm, leadingTerm, relativeError]
    ring
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnp1pos : 0 < (n : ℝ) + 1 := by linarith
    have hrel : ((n : ℝ) - 1) / ((n : ℝ) + 1) - 1 =
        -2 / ((n : ℝ) + 1) := by
      field_simp
      ring
    simp only [relativeError, hrel, Real.norm_eq_abs, abs_neg, abs_div,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hnp1pos,
      abs_of_pos hnpos]
    norm_num only [abs_one]
    rw [mul_one_div]
    apply (div_le_div_iff₀ hnp1pos hnpos).2
    nlinarith

theorem gap2 :
    Asymptotics.IsBigO atTop remainder
      (fun n : ℕ => 1 / Real.rpow n (1 + 1 / 100 : ℝ)) := by
  have hlead : Asymptotics.IsBigO atTop leadingTerm
      (fun n : ℕ => 1 / Real.rpow n (1 / 100 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    simp [leadingTerm, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (Real.rpow_pos_of_pos hnpos _)]
  have hmul := hlead.mul gap1.2
  apply hmul.congr'
  · filter_upwards with n
    rfl
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [show (1 + 1 / 100 : ℝ) = 1 / 100 + 1 by ring]
    have hrpow : Real.rpow n (1 / 100 + 1 : ℝ) =
        Real.rpow n (1 / 100 : ℝ) * (n : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_add hnpos (1 / 100) 1
    rw [hrpow]
    ring

theorem gap3 :
    (∀ n : ℕ, 1 ≤ n → mainTerm n = leadingTerm n + remainder n) ∧
    Asymptotics.IsBigO atTop remainder
      (fun n : ℕ => 1 / Real.rpow n (1 + 1 / 100 : ℝ)) := by
  constructor
  · intro n hn
    rw [gap1.1 n hn]
    simp only [remainder]
    ring
  · exact gap2

theorem gap4 :
    Summable (fun n : ℕ =>
      1 / Real.rpow (n + 1) (1 + 1 / 100 : ℝ)) := by
  have hbase : Summable (fun n : ℕ =>
      1 / Real.rpow n (1 + 1 / 100 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  simpa [Nat.add_comm] using hshift

theorem gap5 :
    ConditionallySummable (fun n : ℕ => leadingTerm (n + 1)) := by
  let amp : ℕ → ℝ := fun n => 1 / Real.rpow (n + 1) (1 / 100 : ℝ)
  have hamp : Antitone amp := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by simp [amp]; positivity)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  have hamp0 : Tendsto amp atTop (nhds 0) := by
    simpa [amp, one_div] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp htop).inv_tendsto_atTop
  have hnegamp : Monotone (fun n => -amp n) := hamp.neg
  rcases hnegamp.tendsto_alternating_series_of_tendsto_zero (by simpa using hamp0.neg) with
    ⟨s, hs⟩
  have hlead : ProofGap.SeriesConverges (fun n : ℕ => leadingTerm (n + 1)) := by
    apply seriesConverges_of_tendsto_sum_range
    apply hs.congr'
    filter_upwards with N
    apply Finset.sum_congr rfl
    intro n hn
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    simp only [leadingTerm, amp, pow_succ, hcast]
    ring
  have hnotabs : ¬ ProofGap.SeriesConverges
      (fun n : ℕ => |leadingTerm (n + 1)|) := by
    intro habs
    have huncond := unconditional_of_seriesConverges_of_nonneg (fun n => abs_nonneg _) habs
    have hampSum : Summable amp := huncond.congr (fun n => by
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      have hrpos : 0 < Real.rpow ((n + 1 : ℕ) : ℝ) (1 / 100 : ℝ) :=
        Real.rpow_pos_of_pos (by positivity) _
      simp only [leadingTerm, amp, abs_div, abs_pow, abs_neg, abs_one, one_pow]
      rw [abs_of_pos hrpos, hcast])
    have hbase : Summable (fun n : ℕ => 1 / Real.rpow n (1 / 100 : ℝ)) :=
      (summable_nat_add_iff 1).mp (by simpa [amp, Nat.add_comm] using hampSum)
    have hp := Real.summable_one_div_nat_rpow.mp hbase
    norm_num at hp
  exact ⟨hlead, hnotabs⟩

theorem gap6 :
    ConditionallySummable (fun n : ℕ => mainTerm (n + 1)) := by
  rcases gap5 with ⟨hlead, hnotleadabs⟩
  have hremO : Asymptotics.IsBigO atTop (fun n : ℕ => remainder (n + 1))
      (fun n : ℕ => 1 / Real.rpow (n + 1) (1 + 1 / 100 : ℝ)) := by
    simpa [Function.comp_def, Nat.add_assoc] using
      gap2.comp_tendsto (tendsto_add_atTop_nat 1)
  have hrem : Summable (fun n : ℕ => remainder (n + 1)) :=
    summable_of_isBigO_nat gap4 hremO
  have hmain : ProofGap.SeriesConverges (fun n : ℕ => mainTerm (n + 1)) := by
    have hsum := hlead.add (seriesConverges_of_summable hrem)
    exact hsum.congr (fun n => (gap3.1 (n + 1) (by omega)).symm)
  have hnotabs : ¬ ProofGap.SeriesConverges
      (fun n : ℕ => |mainTerm (n + 1)|) := by
    intro habs
    have habs' := unconditional_of_seriesConverges_of_nonneg (fun n => abs_nonneg _) habs
    have hmain' : Summable (fun n : ℕ => mainTerm (n + 1)) := habs'.of_abs
    have hlead' : Summable (fun n : ℕ => leadingTerm (n + 1)) := by
      have hsub := hmain'.sub hrem
      exact hsub.congr (fun n => by
        rw [gap3.1 (n + 1) (by omega)]
        ring)
    exact hnotleadabs (seriesConverges_of_summable hlead'.abs)
  exact ⟨hmain, hnotabs⟩

end

end ProofGap.Exercise2683
