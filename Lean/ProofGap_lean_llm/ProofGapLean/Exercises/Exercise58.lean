import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast

open scoped Topology

/-!
# Exercise 58

Semantic formalization of `proof_gap/exercise_58/{1,...,10}.txt`.
The binomial ellipsis is represented by the full finite binomial sum.
-/

namespace ProofGap.Exercise58

noncomputable section

def binomialExpansion (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ)

def lowerTerm (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) / 2

def u (n : ℕ) : ℝ :=
  (n : ℝ) / (2 : ℝ) ^ n

def upper (n : ℕ) : ℝ :=
  2 / ((n : ℝ) - 1)

/-- Source: `proof_gap/exercise_58/1.txt`. -/
theorem gap1 :
    ∀ n : ℕ, (2 : ℝ) ^ n = (1 + 1 : ℝ) ^ n := by
  intro n
  norm_num

/-- Source: `proof_gap/exercise_58/2.txt`. -/
theorem gap2
    (h1 : ∀ n : ℕ, (2 : ℝ) ^ n = (1 + 1 : ℝ) ^ n) :
    ∀ n : ℕ, (1 + 1 : ℝ) ^ n = binomialExpansion n := by
  intro n
  unfold binomialExpansion
  norm_num
  have hcast := congrArg (fun m : ℕ => (m : ℝ))
    (Nat.sum_range_choose n)
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at hcast
  exact hcast.symm

/-- Source: `proof_gap/exercise_58/3.txt`. -/
theorem gap3
    (h2 : ∀ n : ℕ, (1 + 1 : ℝ) ^ n = binomialExpansion n) :
    ∀ n : ℕ, binomialExpansion n > lowerTerm n := by
  intro n
  by_cases hn : n < 2
  · interval_cases n <;>
      norm_num [binomialExpansion, lowerTerm, Finset.sum_range_succ]
  · have hzero : 0 ∈ Finset.range (n + 1) := by simp
    have htwo : 2 ∈ (Finset.range (n + 1)).erase 0 := by
      simp
      omega
    have hle :
        (Nat.choose n 2 : ℝ) ≤
          ∑ k ∈ (Finset.range (n + 1)).erase 0, (Nat.choose n k : ℝ) :=
      Finset.single_le_sum
        (f := fun k => (Nat.choose n k : ℝ))
        (fun k hk => by positivity) htwo
    have hsum :=
      Finset.sum_erase_add (Finset.range (n + 1))
        (fun k => (Nat.choose n k : ℝ)) hzero
    simp only [Nat.choose_zero_right, Nat.cast_one] at hsum
    have hchoose : (Nat.choose n 2 : ℝ) = lowerTerm n := by
      exact Nat.cast_choose_two ℝ n
    unfold binomialExpansion
    rw [← hchoose]
    linarith

/-- Source: `proof_gap/exercise_58/4.txt`. -/
theorem gap4
    (h1 : ∀ n : ℕ, (2 : ℝ) ^ n = (1 + 1 : ℝ) ^ n)
    (h2 : ∀ n : ℕ, (1 + 1 : ℝ) ^ n = binomialExpansion n)
    (h3 : ∀ n : ℕ, binomialExpansion n > lowerTerm n) :
    ∀ n : ℕ, (2 : ℝ) ^ n > lowerTerm n := by
  intro n
  rw [h1 n, h2 n]
  exact h3 n

/-- Source: `proof_gap/exercise_58/5.txt`; positive `n` is restored. -/
theorem gap5 :
    ∀ n : ℕ, 0 < n → 0 < u n := by
  intro n hn
  unfold u
  positivity

/-- Source: `proof_gap/exercise_58/6.txt`; the source condition `n>2` is restored. -/
theorem gap6
    (h4 : ∀ n : ℕ, (2 : ℝ) ^ n > lowerTerm n) :
    ∀ n : ℕ, 2 < n → u n < upper n := by
  intro n hn
  have hnreal : 0 < (n : ℝ) := by positivity
  have hsub : 0 < (n : ℝ) - 1 := by
    have hncast : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  unfold u upper
  apply (div_lt_div_iff₀ hpow hsub).2
  unfold lowerTerm at h4
  nlinarith [h4 n]

/-- Source: `proof_gap/exercise_58/7.txt`; a valid denominator condition is restored. -/
theorem gap7 :
    ∀ n : ℕ, 1 < n → 0 < upper n := by
  intro n hn
  unfold upper
  have hncast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact div_pos (by norm_num) (by linarith)

/-- Source: `proof_gap/exercise_58/8.txt`. -/
theorem gap8 :
    Tendsto upper atTop (𝓝 0) := by
  have hmap : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with n hn
    omega
  have hlim :
      Tendsto (fun n : ℕ => (2 : ℝ) / ((n - 1 : ℕ) : ℝ))
        atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hmap
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  unfold upper
  rw [Nat.cast_sub hn]
  norm_num

/-- Source: `proof_gap/exercise_58/9.txt`. -/
theorem gap9
    (h5 : ∀ n : ℕ, 0 < n → 0 < u n)
    (h6 : ∀ n : ℕ, 2 < n → u n < upper n)
    (h8 : Tendsto upper atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact (h5 n hn).le
  · filter_upwards [Filter.eventually_gt_atTop 2] with n hn
    exact (h6 n hn).le
  · exact h8

/-- Source: `proof_gap/exercise_58/10.txt`. -/
theorem gap10
    (h9 : Tendsto u atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  exact h9

end

end ProofGap.Exercise58
