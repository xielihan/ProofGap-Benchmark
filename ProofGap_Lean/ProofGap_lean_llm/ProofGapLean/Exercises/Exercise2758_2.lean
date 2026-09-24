import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2758_2

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(x - n) ^ 2)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x
  unfold term
  apply Real.tendsto_exp_atBot.comp
  refine tendsto_atBot.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (x + |b| + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hdist : |b| + 1 < (n : ℝ) - x := by
    linarith
  have ht0 : 0 ≤ (n : ℝ) - x := by
    linarith [abs_nonneg b]
  have ht1 : 1 ≤ (n : ℝ) - x := by
    linarith [abs_nonneg b]
  have hmul :
      0 ≤ ((n : ℝ) - x) * (((n : ℝ) - x) - 1) :=
    mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hsquare : |b| ≤ ((n : ℝ) - x) ^ 2 := by
    nlinarith
  have hbound : -b ≤ ((n : ℝ) - x) ^ 2 :=
    le_trans (neg_le_abs b) hsquare
  nlinarith

theorem gap2 :
    ∀ x : ℝ, (0 : ℝ) = 0 := by
  intro x
  rfl

theorem gap3 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (ε₀ : ℝ), 0 < ε₀ → ε₀ < 1 → |term n n| = 1 := by
  intro n ε₀ hε₀ hε₀'
  simp [term]

theorem gap5 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → 1 > ε₀ := by
  intro ε₀ hε₀ hε₀'
  exact hε₀'

theorem gap6 :
    ∀ (n : ℕ) (ε₀ : ℝ), 0 < ε₀ → ε₀ < 1 → |term n n| > ε₀ := by
  intro n ε₀ hε₀ hε₀'
  rw [gap4 n ε₀ hε₀ hε₀']
  exact hε₀'

theorem gap7 :
    ¬ UniformlyConvergesOn term (fun _ => 0) Set.univ := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  have hs := hN (N + 1) (by simpa using Nat.lt_succ_self N)
      (N + 1) (by simp)
  have hsmall : |term (N + 1) (N + 1)| < (1 / 2 : ℝ) := by
    simpa using hs
  have hlarge : |term (N + 1) (N + 1)| > (1 / 2 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (gap6 (N + 1) (1 / 2) (by norm_num) (by norm_num))
  linarith

theorem gap8 :
    ¬ UniformlyConvergesOn term (fun _ => 0) Set.univ := by
  exact gap7

end

end ProofGap.Exercise2758_2
