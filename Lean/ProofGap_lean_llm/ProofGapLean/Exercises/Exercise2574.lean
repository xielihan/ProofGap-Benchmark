import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace ProofGap.Exercise2574

noncomputable section

def term (x : ℝ) (n : ℕ) : ℝ :=
  Real.sin ((n : ℝ) * x) / (2 : ℝ) ^ n

def partialSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, term x (j + 1)

def block (x : ℝ) (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range p, term x (n + j + 1)

def geometricBlock (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range p, 1 / (2 : ℝ) ^ (n + j + 1)

private lemma geometricBlock_closed_form (n p : ℕ) :
    geometricBlock n p =
      1 / (2 : ℝ) ^ n - 1 / (2 : ℝ) ^ (n + p) := by
  induction p with
  | zero =>
      simp [geometricBlock]
  | succ p ih =>
      rw [geometricBlock, Finset.sum_range_succ]
      change geometricBlock n p + _ = _
      rw [ih]
      simp only [Nat.add_succ, Nat.add_zero, pow_succ]
      field_simp <;> ring

private lemma cast_succ_le_two_pow (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, pow_succ] at ih ⊢
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith

theorem gap1 :
    ∀ x n p, |partialSum x (n + p) - partialSum x n| =
      |block x n p| := by
  intro x n p
  simp [partialSum, block, Finset.sum_range_add]

theorem gap2
    (hblock : ∀ x n p, |partialSum x (n + p) - partialSum x n| =
      |block x n p|) :
    ∀ x n p, |partialSum x (n + p) - partialSum x n| ≤
      geometricBlock n p := by
  intro x n p
  rw [hblock x n p]
  unfold block geometricBlock term
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

theorem gap3 :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 1 ≤ N ∧
      ∀ n > N, ∀ p ≥ 1, geometricBlock n p < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  refine ⟨max k 1, Nat.le_max_right _ _, ?_⟩
  intro n hn p hp
  have hkn : k < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
  have hknR : (k : ℝ) < (n : ℝ) := by
    exact_mod_cast hkn
  have hratio : 1 / ε < (n : ℝ) := lt_trans hk hknR
  have hone : 1 < ε * (n : ℝ) := by
    have h := (div_lt_iff₀ hε).1 hratio
    simpa [mul_comm] using h
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    have h := cast_succ_le_two_pow n
    norm_num [Nat.cast_add, Nat.cast_one] at h
    linarith
  have hmul : ε * (n : ℝ) ≤ ε * (2 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt hε)
  have honepow : 1 < ε * (2 : ℝ) ^ n := lt_of_lt_of_le hone hmul
  have hdecay : 1 / (2 : ℝ) ^ n < ε := by
    exact (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).2 honepow
  calc
    geometricBlock n p =
        1 / (2 : ℝ) ^ n - 1 / (2 : ℝ) ^ (n + p) :=
      geometricBlock_closed_form n p
    _ < 1 / (2 : ℝ) ^ n := sub_lt_self _ (by positivity)
    _ < ε := hdecay

theorem gap4
    (hbound : ∀ x n p, |partialSum x (n + p) - partialSum x n| ≤
      geometricBlock n p)
    (hsmall : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 1 ≤ N ∧
      ∀ n > N, ∀ p ≥ 1, geometricBlock n p < ε) :
    ∀ x ε, ε > 0 → ∃ N : ℕ, ∀ n > N, ∀ p ≥ 1,
      |partialSum x (n + p) - partialSum x n| < ε := by
  intro x ε hε
  obtain ⟨N, hN, hsmallN⟩ := hsmall ε hε
  refine ⟨N, ?_⟩
  intro n hn p hp
  exact lt_of_le_of_lt (hbound x n p) (hsmallN n hn p hp)

theorem gap5
    (hcauchy : ∀ x ε, ε > 0 → ∃ N : ℕ, ∀ n > N, ∀ p ≥ 1,
      |partialSum x (n + p) - partialSum x n| < ε) :
    ∀ x, Summable (term x) := by
  intro x
  have hg : Summable (fun n : ℕ => 1 / (2 : ℝ) ^ n) := by
    have hg' : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) :=
      summable_geometric_of_norm_lt_one (by
        norm_num [Real.norm_eq_abs])
    simpa [one_div, inv_pow] using hg'
  refine Summable.of_norm_bounded hg ?_
  intro n
  unfold term
  rw [Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

theorem gap6
    (hsum : ∀ x, Summable (term x)) :
    ∀ x, Summable (term x) := by
  intro x
  exact hsum x

end

end ProofGap.Exercise2574
