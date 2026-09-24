import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2772

noncomputable section

open scoped BigOperators

def term (x : ℝ) (n : ℕ) : ℝ :=
  1 / ((x + n) * (x + n + 1))

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

private theorem shiftedTermIdentity (x : ℝ) (hx : 0 < x) (n : ℕ) :
    term x (n + 1) =
      1 / (x + (n : ℝ) + 1) - 1 / (x + (n : ℝ) + 2) := by
  unfold term
  norm_num [Nat.cast_add, Nat.cast_one]
  have h₁ : x + (n : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : x + (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h₁, h₂]
  <;> ring

private theorem sumShiftedTerm (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (∑ k ∈ Finset.range n, term x (k + 1)) =
      1 / (x + 1) - 1 / (x + (n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, shiftedTermIdentity x hx n]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private theorem tendstoShiftedInvZero (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (fun n : ℕ => 1 / (x + (n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / ε < (N : ℝ) := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < x + (n : ℝ) + 1 := by positivity
  have hbound : 1 / ε < x + (n : ℝ) + 1 := by nlinarith
  have hone : 1 < (x + (n : ℝ) + 1) * ε :=
    (div_lt_iff₀ hε).mp hbound
  have hsmall : 1 / (x + (n : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).2
    simpa [mul_comm] using hone
  rw [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.mpr hden)]
  exact hsmall

private theorem shiftedTermHasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => term x (n + 1)) (1 / (x + 1)) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ term x (n + 1) := by
    intro n
    unfold term
    positivity
  refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg (1 / (x + 1))).2 ?_
  have hconst :
      Filter.Tendsto (fun _ : ℕ => 1 / (x + 1)) Filter.atTop
        (nhds (1 / (x + 1))) :=
    tendsto_const_nhds
  have hlim := hconst.sub (tendstoShiftedInvZero x hx)
  simpa only [sumShiftedTerm x hx, sub_zero] using hlim

theorem gap1 (x : ℝ) (n : ℕ) (hx : 0 < x) (hn : 1 ≤ n) :
    |term x n| < 1 / (n : ℝ) ^ 2 := by
  unfold term
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hxn : 0 < x + (n : ℝ) := by linarith
  have hxn1 : 0 < x + (n : ℝ) + 1 := by linarith
  have hprod : 0 < (x + (n : ℝ)) * (x + (n : ℝ) + 1) :=
    mul_pos hxn hxn1
  have hsq : 0 < (n : ℝ) ^ 2 := pow_pos hn0 2
  rw [abs_of_pos (one_div_pos.mpr hprod)]
  apply (div_lt_div_iff₀ hprod hsq).2
  have hmul : 0 < x * (n : ℝ) := mul_pos hx hn0
  nlinarith [sq_nonneg x]

theorem gap2 :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hmajor : Summable (fun n : ℕ => 2 * term 1 (n + 1)) :=
    ((shiftedTermHasSum (1 : ℝ) zero_lt_one).mul_left 2).summable
  have htail :
      Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmajor
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h₂ : 0 < (n : ℝ) + 2 := by positivity
    have h₃ : 0 < (n : ℝ) + 3 := by positivity
    have hineq :
        1 / ((n : ℝ) + 2) ^ 2 ≤
          2 / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos h₂) (mul_pos h₂ h₃)).2
      nlinarith
    calc
      1 / (((n + 2 : ℕ) : ℝ) ^ 2) =
          1 / ((n : ℝ) + 2) ^ 2 := by norm_num [Nat.cast_add]
      _ ≤ 2 / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := hineq
      _ = 2 * term 1 (n + 1) := by
        unfold term
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp [ne_of_gt h₂, ne_of_gt h₃]
        <;> ring
  apply (summable_nat_add_iff 1).1
  simpa [Nat.add_assoc] using htail

theorem gap3 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) gap2
  exact (gap1 x (n + 1) hx (Nat.succ_le_succ (Nat.zero_le n))).le

theorem gap4 :
    SeriesUniformlyConvergesOn
      (fun n x => term x (n + 1))
      (Set.Ioi (0 : ℝ))
      (fun x => ∑' n : ℕ, term x (n + 1)) := by
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / ε < (N : ℝ) := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hx' : 0 < x := hx
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < x + (n : ℝ) + 2 := by positivity
  have hbound : 1 / ε < x + (n : ℝ) + 2 := by
    nlinarith [hN, hn']
  have hone : 1 < (x + (n : ℝ) + 2) * ε :=
    (div_lt_iff₀ hε).mp hbound
  have hsmall : 1 / (x + (n : ℝ) + 2) < ε := by
    apply (div_lt_iff₀ hden).2
    simpa [mul_comm] using hone
  have herr :
      (∑ k ∈ Finset.range (n + 1), term x (k + 1)) -
          (∑' k : ℕ, term x (k + 1)) =
        -(1 / (x + (n : ℝ) + 2)) := by
    rw [(shiftedTermHasSum x hx').tsum_eq,
      sumShiftedTerm x hx' (n + 1)]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [herr, abs_neg, abs_of_pos (one_div_pos.mpr hden)]
  exact hsmall

theorem gap5 :
    (∀ x ∈ Set.Ioi (0 : ℝ),
      Summable (fun n : ℕ => |term x (n + 1)|)) ∧
    SeriesUniformlyConvergesOn
      (fun n x => term x (n + 1))
      (Set.Ioi (0 : ℝ))
      (fun x => ∑' n : ℕ, term x (n + 1)) := by
  constructor
  · intro x hx
    exact gap3 x hx
  · exact gap4

end

end ProofGap.Exercise2772
