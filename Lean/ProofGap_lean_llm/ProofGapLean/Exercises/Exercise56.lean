import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology

/-!
# Exercise 56

Semantic formalization of `proof_gap/exercise_56/{1,...,7}.txt`.
-/

namespace ProofGap.Exercise56

noncomputable section

def telescopingSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / ((k : ℝ) * ((k : ℝ) + 1))

def closed (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 1)

def SameLimit (u v : ℕ → ℝ) : Prop :=
  ∀ l : ℝ, Tendsto u atTop (𝓝 l) ↔ Tendsto v atTop (𝓝 l)

/-- Source: `proof_gap/exercise_56/1.txt`. -/
theorem gap1 :
    (1 / (1 * 2) : ℝ) = 1 - 1 / 2 := by
  norm_num

/-- Source: `proof_gap/exercise_56/2.txt`. -/
theorem gap2
    (h1 : (1 / (1 * 2) : ℝ) = 1 - 1 / 2) :
    (1 / (2 * 3) : ℝ) = 1 / 2 - 1 / 3 := by
  norm_num

/-- Source: `proof_gap/exercise_56/3.txt`; positive `n` is restored. -/
theorem gap3 :
    ∀ n : ℕ, 0 < n →
      1 / ((n : ℝ) * ((n : ℝ) + 1)) =
        1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
  intro n hn
  have hnreal : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp [hnreal]
  ring

/-- Source: `proof_gap/exercise_56/4.txt`. -/
theorem gap4
    (h3 : ∀ n : ℕ, 0 < n →
      1 / ((n : ℝ) * ((n : ℝ) + 1)) =
        1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) :
    ∀ n : ℕ, 0 < n → telescopingSum n = closed n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hnzero : n = 0
      · subst n
        norm_num [telescopingSum, closed]
      · rw [telescopingSum, Finset.sum_Icc_succ_top (by omega)]
        change
          telescopingSum n +
              1 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) =
            closed (n + 1)
        rw [ih (Nat.pos_of_ne_zero hnzero), h3 (n + 1) (by omega)]
        unfold closed
        simp only [Nat.cast_add, Nat.cast_one]
        ring

/-- Source: `proof_gap/exercise_56/5.txt`. -/
theorem gap5
    (h4 : ∀ n : ℕ, 0 < n → telescopingSum n = closed n) :
    SameLimit telescopingSum closed := by
  have heq : telescopingSum =ᶠ[atTop] closed := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact h4 n hn
  intro l
  exact Filter.tendsto_congr' heq

/-- Source: `proof_gap/exercise_56/6.txt`. -/
theorem gap6
    (h5 : SameLimit telescopingSum closed) :
    Tendsto closed atTop (𝓝 1) := by
  unfold closed
  simpa using
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Source: `proof_gap/exercise_56/7.txt`. -/
theorem gap7
    (h5 : SameLimit telescopingSum closed)
    (h6 : Tendsto closed atTop (𝓝 1)) :
    Tendsto telescopingSum atTop (𝓝 1) := by
  exact (h5 1).mpr h6

end

end ProofGap.Exercise56
