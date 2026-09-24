import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2669

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Real.sqrt n / (n + 100)

def leadingTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / Real.sqrt n

def comparison (n : ℕ) : ℝ :=
  1 / Real.rpow n (3 / 2 : ℝ)

private theorem seriesConverges_of_tendsto_sum_range {f : ℕ → ℝ}
    (h : ∃ l, Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 l)) :
    ProofGap.SeriesConverges f := by
  rcases h with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
  exact hl

theorem gap1 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => term (n + 1) - leadingTerm (n + 1))
      (fun n : ℕ => comparison (n + 1)) := by
  refine Asymptotics.IsBigO.of_bound 100 (.of_forall fun n => ?_)
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hm
  have hsum : (0 : ℝ) < (n : ℝ) + 1 + 100 := by positivity
  have hs_sq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt hm.le
  have hrpow :
      Real.rpow ((n : ℝ) + 1) (3 / 2 : ℝ) =
        ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) := by
    calc
      Real.rpow ((n : ℝ) + 1) (3 / 2 : ℝ) =
          Real.rpow ((n : ℝ) + 1) (1 + 1 / 2 : ℝ) := by norm_num
      _ = Real.rpow ((n : ℝ) + 1) 1 * Real.rpow ((n : ℝ) + 1) (1 / 2) :=
        Real.rpow_add hm 1 (1 / 2)
      _ = ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) := by
        congr 1
        · exact Real.rpow_one _
        · exact (Real.sqrt_eq_rpow _).symm
  have hdiff :
      term (n + 1) - leadingTerm (n + 1) =
        (-100 : ℝ) * (-1 : ℝ) ^ (n + 1) /
          ((n : ℝ) + 1 + 100) / Real.sqrt ((n : ℝ) + 1) := by
    simp only [term, leadingTerm, Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hs, ne_of_gt hsum]
    nlinarith [hs_sq]
  have hden :
      ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) ≤
        ((n : ℝ) + 1 + 100) * Real.sqrt ((n : ℝ) + 1) := by
    nlinarith
  have hone :
      1 / (((n : ℝ) + 1 + 100) * Real.sqrt ((n : ℝ) + 1)) ≤
        1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) :=
    one_div_le_one_div_of_le (mul_pos hm hs) hden
  calc
    ‖term (n + 1) - leadingTerm (n + 1)‖ =
        100 * (1 / (((n : ℝ) + 1 + 100) * Real.sqrt ((n : ℝ) + 1))) := by
      rw [hdiff]
      simp [Real.norm_eq_abs, abs_of_pos hsum, abs_of_pos hs, div_eq_mul_inv]
      ring
    _ ≤ 100 * (1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hone (by norm_num)
    _ = 100 * ‖comparison (n + 1)‖ := by
      rw [comparison, Nat.cast_add, Nat.cast_one, hrpow]
      simp [Real.norm_eq_abs, abs_of_pos hm, abs_of_pos hs, div_eq_mul_inv]

theorem gap2 :
    ProofGap.SeriesConverges (fun n : ℕ => leadingTerm (n + 1)) := by
  let f : ℕ → ℝ := fun n => 1 / Real.sqrt (n + 1)
  have hf_antitone : Antitone f := by
    intro a b hab
    dsimp [f]
    gcongr
  have hf_zero : Tendsto f atTop (𝓝 0) := by
    simpa [f, one_div, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  have hAlt : ProofGap.SeriesConverges (fun n => (-1 : ℝ) ^ n * f n) :=
    seriesConverges_of_tendsto_sum_range
      (hf_antitone.tendsto_alternating_series_of_tendsto_zero hf_zero)
  refine hAlt.neg.congr fun n => ?_
  simp [leadingTerm, f, pow_succ, div_eq_mul_inv]

theorem gap3 :
    Summable (fun n : ℕ => comparison (n + 1)) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  simpa [comparison, one_div] using (summable_nat_add_iff (f := fun n : ℕ =>
    ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) 1).mpr h

theorem gap4 :
    ProofGap.SeriesConverges (fun n : ℕ => term (n + 1)) := by
  have hError : Summable (fun n : ℕ => term (n + 1) - leadingTerm (n + 1)) :=
    summable_of_isBigO gap3 (by simpa only [Nat.cofinite_eq_atTop] using gap1)
  have hErrorConditional :
      Summable (fun n : ℕ => term (n + 1) - leadingTerm (n + 1))
        (SummationFilter.conditional ℕ) :=
    hError.mono_filter (SummationFilter.conditional ℕ).le_atTop
  refine gap2.add hErrorConditional |>.congr fun n => ?_
  ring

end

end ProofGap.Exercise2669
