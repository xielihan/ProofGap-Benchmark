import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2701

noncomputable section

open Filter

def comparisonTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / Real.sqrt (n + 1)

def perturbedTerm (n : ℕ) : ℝ :=
  comparisonTerm n + 1 / ((n : ℝ) + 1)

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

theorem gap1 :
    ∀ a b : ℕ → ℝ,
      (∀ n, 0 < a n) → (∀ n, 0 < b n) →
      Summable a →
      Tendsto (fun n => b n / a n) atTop (nhds 1) →
      Summable b := by
  intro a b ha hb hsum hratio
  have hlt : ∀ᶠ n in atTop, b n / a n < 2 :=
    (tendsto_order.1 hratio).2 2 (by norm_num)
  rcases (eventually_atTop.1 hlt) with ⟨N, hN⟩
  have haShift : Summable (fun n : ℕ => a (n + N)) :=
    (summable_nat_add_iff N).2 hsum
  have hbShift : Summable (fun n : ℕ => b (n + N)) :=
    (haShift.mul_left 2).of_nonneg_of_le
      (fun n => (hb (n + N)).le)
      (fun n => by
        exact ((div_lt_iff₀ (ha (n + N))).1 (hN (n + N) (by omega))).le)
  exact (summable_nat_add_iff N).1 hbShift

theorem gap2 :
    ProofGap.SeriesConverges comparisonTerm := by
  let amp : ℕ → ℝ := fun n => 1 / Real.sqrt (n + 1)
  have hamp : Antitone amp := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by simp; positivity)
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hmn 1
  have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  have hamp0 : Tendsto amp atTop (nhds 0) := by
    simpa [amp, one_div] using
      (Real.tendsto_sqrt_atTop.comp htop).inv_tendsto_atTop
  have hnegamp : Monotone (fun n => -amp n) := hamp.neg
  rcases hnegamp.tendsto_alternating_series_of_tendsto_zero (by simpa using hamp0.neg) with
    ⟨s, hs⟩
  apply seriesConverges_of_tendsto_sum_range
  apply hs.congr'
  filter_upwards with N
  apply Finset.sum_congr rfl
  intro n hn
  simp only [comparisonTerm, amp, pow_succ]
  ring

theorem gap3 :
    Tendsto (fun n : ℕ => perturbedTerm n / comparisonTerm n)
      atTop (nhds 1) := by
  have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  have hamp0 : Tendsto (fun n : ℕ => 1 / Real.sqrt (n + 1)) atTop (nhds 0) := by
    simpa [one_div] using
      (Real.tendsto_sqrt_atTop.comp htop).inv_tendsto_atTop
  have hcomp0 : Tendsto comparisonTerm atTop (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simpa [comparisonTerm, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hamp0
  have hratio : ∀ n : ℕ,
      perturbedTerm n / comparisonTerm n = 1 + comparisonTerm n := by
    intro n
    have hxpos : 0 < (n : ℝ) + 1 := by positivity
    have hsqrtpos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 hxpos
    have hsquare : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) =
        (n : ℝ) + 1 := Real.mul_self_sqrt hxpos.le
    have hsign : (-1 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hsignsq :
        (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    simp only [perturbedTerm, comparisonTerm]
    field_simp
    nlinarith [hsquare, hsignsq]
  have hsum : Tendsto (fun n : ℕ => 1 + comparisonTerm n) atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hcomp0
  simpa only [add_zero] using
    hsum.congr' (Eventually.of_forall fun n => (hratio n).symm)

theorem gap4 :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro h
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff 1).1 (by
      simpa only [Nat.cast_add, Nat.cast_one] using h)
  exact Real.not_summable_one_div_natCast hbase

theorem gap5 :
    ¬ ProofGap.SeriesConverges perturbedTerm := by
  intro hpert
  have hharm : ProofGap.SeriesConverges (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    have hsub := hpert.sub gap2
    exact hsub.congr (fun n => by simp [perturbedTerm])
  have hsum := unconditional_of_seriesConverges_of_nonneg (fun n => by positivity) hharm
  exact gap4 hsum

theorem gap6 :
    (∀ a b : ℕ → ℝ,
      (∀ n, 0 < a n) → (∀ n, 0 < b n) →
      Summable a →
      Tendsto (fun n => b n / a n) atTop (nhds 1) →
      Summable b) ∧
    (∃ a b : ℕ → ℝ,
      ProofGap.SeriesConverges a ∧
      Tendsto (fun n => b n / a n) atTop (nhds 1) ∧
      ¬ ProofGap.SeriesConverges b) := by
  exact ⟨gap1, comparisonTerm, perturbedTerm, gap2, gap3, gap5⟩

end

end ProofGap.Exercise2701
