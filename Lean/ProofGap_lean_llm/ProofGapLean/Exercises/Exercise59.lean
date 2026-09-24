import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology

/-!
# Exercise 59

Semantic formalization of Exercise 59, gaps 1,...,7.
-/

namespace ProofGap.Exercise59

noncomputable section

def u (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / (Nat.factorial n : ℝ)

def factorProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (2 : ℝ) / (k : ℝ)

def upper (n : ℕ) : ℝ :=
  4 / (n : ℝ)

/-- Exercise 59, gap 1. -/
theorem gap1 :
    ∀ n : ℕ, 0 < u n := by
  intro n
  unfold u
  positivity

/-- Exercise 59, gap 2. -/
theorem gap2
    (h1 : ∀ n : ℕ, 0 < u n) :
    ∀ n : ℕ, u n = factorProduct n := by
  intro n
  induction n with
  | zero =>
      norm_num [u, factorProduct]
  | succ n ih =>
      rw [factorProduct, Finset.prod_Icc_succ_top (by omega)]
      change
        u (n + 1) =
          factorProduct n * ((2 : ℝ) / ((n + 1 : ℕ) : ℝ))
      rw [← ih]
      unfold u
      rw [Nat.factorial_succ, pow_succ]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp

/-- Exercise 59, gap 3; a positive index is restored. -/
theorem gap3
    (h2 : ∀ n : ℕ, u n = factorProduct n) :
    ∀ n : ℕ, 0 < n → factorProduct n ≤ upper n := by
  intro n hn
  rw [← h2 n]
  by_cases hone : n = 1
  · subst n
    norm_num [u, upper]
  · have htwo : 2 ≤ n := by omega
    have hnat : 2 ^ (n - 2) ≤ Nat.factorial (n - 1) := by
      have hbase := @Nat.factorial_mul_pow_le_factorial 1 (n - 2)
      simpa [show 1 + (n - 2) = n - 1 by omega] using hbase
    have hcast :
        (2 : ℝ) ^ (n - 2) ≤ (Nat.factorial (n - 1) : ℝ) := by
      exact_mod_cast hnat
    have hpow : (2 : ℝ) ^ n = 4 * (2 : ℝ) ^ (n - 2) := by
      rw [show n = (n - 2) + 2 by omega, pow_add]
      norm_num
      ring
    have hfac :
        (Nat.factorial n : ℝ) =
          (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
      rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ]
      norm_num
    have hnreal : 0 < (n : ℝ) := by positivity
    unfold u upper
    apply (div_le_div_iff₀ (by positivity) hnreal).2
    rw [hpow, hfac]
    have hmul :
        (n : ℝ) * (2 : ℝ) ^ (n - 2) ≤
          (n : ℝ) * (Nat.factorial (n - 1) : ℝ) :=
      mul_le_mul_of_nonneg_left hcast hnreal.le
    nlinarith

/-- Exercise 59, gap 4; a positive index is restored. -/
theorem gap4 :
    ∀ n : ℕ, 0 < n → 0 < upper n := by
  intro n hn
  unfold upper
  positivity

/-- Exercise 59, gap 5. -/
theorem gap5 :
    Tendsto upper atTop (𝓝 0) := by
  unfold upper
  exact tendsto_const_div_atTop_nhds_zero_nat 4

/-- Exercise 59, gap 6. -/
theorem gap6
    (h1 : ∀ n : ℕ, 0 < u n)
    (h2 : ∀ n : ℕ, u n = factorProduct n)
    (h3 : ∀ n : ℕ, 0 < n → factorProduct n ≤ upper n)
    (h5 : Tendsto upper atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  apply squeeze_zero' (f := u) (g := upper)
  · exact Filter.Eventually.of_forall fun n => (h1 n).le
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [h2 n]
    exact h3 n hn
  · exact h5

/-- Exercise 59, gap 7. -/
theorem gap7
    (h6 : Tendsto u atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  exact h6

end

end ProofGap.Exercise59
