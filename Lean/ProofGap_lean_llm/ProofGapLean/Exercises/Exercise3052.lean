import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3052

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 3 - 1) / ((n : ℝ) ^ 3 + 1)

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 2 n, factor i

def HasProduct (L : ℝ) : Prop :=
  Tendsto partialProduct atTop (𝓝 L)

theorem gap1 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    ∀ n, P n = partialProduct n := by
  exact hP

theorem gap2 (n : ℕ) :
    partialProduct n =
      ∏ i ∈ Finset.Icc 2 n,
        (((i : ℝ) ^ 3 - 1) / ((i : ℝ) ^ 3 + 1)) := by
  rfl

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    partialProduct n =
      (2 / 3 : ℝ) * (((n : ℝ) ^ 2 + n + 1) / ((n : ℝ) * (n + 1))) := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [partialProduct, factor]
  | succ n hn ih =>
      have hprod :
          partialProduct (n + 1) = partialProduct n * factor (n + 1) := by
        unfold partialProduct
        rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ hn)]
      have hnR : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hnR1 : (0 : ℝ) < (n : ℝ) + 1 := by
        positivity
      have hcub : (0 : ℝ) < ((n : ℝ) + 1) ^ 3 + 1 := by
        positivity
      rw [hprod, ih]
      unfold factor
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hnR, ne_of_gt hnR1, ne_of_gt hcub] <;> ring

theorem gap4 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n)
    (n : ℕ) (hn : 1 ≤ n) :
    P n =
      (2 / 3 : ℝ) * (((n : ℝ) ^ 2 + n + 1) / ((n : ℝ) * (n + 1))) := by
  calc
    P n = partialProduct n := hP n
    _ = (2 / 3 : ℝ) * (((n : ℝ) ^ 2 + n + 1) / ((n : ℝ) * (n + 1))) :=
      gap3 n hn

theorem gap5 :
    Tendsto partialProduct atTop (𝓝 (2 / 3 : ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (Nat.le_max_left N 1) hn
  have hnone : 1 ≤ n := le_trans (Nat.le_max_right N 1) hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnN
  have hbound : 1 / ε < (n : ℝ) := lt_of_lt_of_le hN hcast
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnone)
  have hnp1pos : (0 : ℝ) < (n : ℝ) + 1 := by
    linarith
  have hmul' : (1 : ℝ) < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hbound
  have hmul : (1 : ℝ) < ε * (n : ℝ) := by
    simpa [mul_comm] using hmul'
  have hdiff :
      (2 / 3 : ℝ) *
            (((n : ℝ) ^ 2 + n + 1) / ((n : ℝ) * (n + 1))) -
          2 / 3 =
        2 / (3 * ((n : ℝ) * (n + 1))) := by
    field_simp [ne_of_gt hnpos, ne_of_gt hnp1pos] <;> ring
  have hdenpos :
      (0 : ℝ) < 3 * ((n : ℝ) * ((n : ℝ) + 1)) := by
    positivity
  rw [gap3 n hnone, Real.dist_eq, hdiff,
    abs_of_pos (div_pos (by norm_num) hdenpos)]
  refine (div_lt_iff₀ hdenpos).2 ?_
  have hA : (1 : ℝ) ≤ ε * (n : ℝ) := le_of_lt hmul
  have hB : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    linarith
  have hprod :
      (1 : ℝ) * 1 ≤ (ε * (n : ℝ)) * ((n : ℝ) + 1) := by
    exact mul_le_mul hA hB (by norm_num) (by linarith)
  calc
    (2 : ℝ) < 3 * (1 * 1) := by norm_num
    _ ≤ 3 * ((ε * (n : ℝ)) * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = ε * (3 * ((n : ℝ) * ((n : ℝ) + 1))) := by ring

theorem gap6 : HasProduct (2 / 3 : ℝ) := by
  exact gap5

theorem gap7 : HasProduct (2 / 3 : ℝ) := by
  exact gap6

end

end ProofGap.Exercise3052
