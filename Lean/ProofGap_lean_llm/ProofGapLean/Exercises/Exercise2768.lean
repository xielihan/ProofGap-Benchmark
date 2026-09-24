import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2768

noncomputable section

open Filter
open scoped BigOperators

def term (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (n : ℝ) ^ 2

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

theorem gap1 (x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hn : 1 ≤ n) :
    |term x n| ≤ 1 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
  rw [term]
  simp only [abs_div, abs_pow, abs_of_pos hn0]
  apply (div_le_div_iff_of_pos_right (pow_pos hn0 2)).2
  exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)

theorem gap2 :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  simpa only [Function.comp_apply] using
    (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective

theorem gap3 (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  exact gap2.of_nonneg_of_le (fun _ => abs_nonneg _) fun n =>
    gap1 x (n + 1) hx (Nat.succ_le_succ (Nat.zero_le n))

theorem gap4 :
    SeriesUniformlyConvergesOn
      (fun n x => term x (n + 1))
      (Set.Icc (-1 : ℝ) 1)
      (fun x => ∑' n : ℕ, term x (n + 1)) := by
  have hU := tendstoUniformlyOn_tsum_nat
    (f := fun n x => term x (n + 1)) gap2
    (fun n x hx => by
      simpa [Real.norm_eq_abs] using
        gap1 x (n + 1) hx (Nat.succ_le_succ (Nat.zero_le n)))
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hU ε hε)
  refine ⟨N, fun n hn x hx => ?_⟩
  simpa [Real.dist_eq, abs_sub_comm] using hN (n + 1) (hn.trans (Nat.le_succ n)) x hx

theorem gap5 :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Summable (fun n : ℕ => |term x (n + 1)|)) ∧
    SeriesUniformlyConvergesOn
      (fun n x => term x (n + 1))
      (Set.Icc (-1 : ℝ) 1)
      (fun x => ∑' n : ℕ, term x (n + 1)) := by
  exact ⟨gap3, gap4⟩

end

end ProofGap.Exercise2768
