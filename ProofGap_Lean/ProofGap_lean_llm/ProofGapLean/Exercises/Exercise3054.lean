import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3054

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ :=
  1 + (1 / 2 : ℝ) ^ (2 ^ n)

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range (n + 1), factor i

def HasProduct (L : ℝ) : Prop :=
  Tendsto partialProduct atTop (𝓝 L)

theorem gap1 (n : ℕ) :
    (1 - (1 / 2 : ℝ)) * partialProduct n =
      (1 - (1 / 2 : ℝ)) *
        ∏ i ∈ Finset.range (n + 1), (1 + (1 / 2 : ℝ) ^ (2 ^ i)) := by
  rfl

theorem gap2 (n : ℕ) :
    (1 - (1 / 2 : ℝ)) *
        (∏ i ∈ Finset.range (n + 1), (1 + (1 / 2 : ℝ) ^ (2 ^ i))) =
      1 - (1 / 2 : ℝ) ^ (2 ^ (n + 1)) := by
  induction n with
  | zero =>
      norm_num [Finset.prod_range_succ]
  | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih]
      have hexp :
          (2 : ℕ) ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 := by
        rw [pow_succ]
      rw [hexp, pow_mul]
      ring

theorem gap3 (n : ℕ) :
    (1 - (1 / 2 : ℝ)) * partialProduct n =
      1 - (1 / 2 : ℝ) ^ (2 ^ (n + 1)) := by
  calc
    (1 - (1 / 2 : ℝ)) * partialProduct n =
        (1 - (1 / 2 : ℝ)) *
          ∏ i ∈ Finset.range (n + 1), (1 + (1 / 2 : ℝ) ^ (2 ^ i)) := gap1 n
    _ = 1 - (1 / 2 : ℝ) ^ (2 ^ (n + 1)) := gap2 n

theorem gap4 (n : ℕ) :
    partialProduct n =
      (1 - (1 / 2 : ℝ) ^ (2 ^ (n + 1))) / (1 - (1 / 2 : ℝ)) := by
  apply (eq_div_iff (by norm_num : (1 - (1 / 2 : ℝ)) ≠ 0)).2
  simpa [mul_comm] using gap3 n

theorem gap5 :
    Tendsto partialProduct atTop (𝓝 (1 / (1 - (1 / 2 : ℝ)))) := by
  have hbound : ∀ n : ℕ, n + 1 ≤ 2 ^ (n + 1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        change n + 1 + 1 ≤ 2 ^ (n + 1 + 1)
        rw [pow_succ]
        omega
  have h_exp :
      Tendsto (fun n : ℕ => (2 : ℕ) ^ (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact le_trans hn (le_trans (Nat.le_succ n) (hbound n))
  have h_pow :
      Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    norm_num [Real.norm_eq_abs]
  have hp :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (2 ^ (n + 1))) atTop (𝓝 0) :=
    h_pow.comp h_exp
  have hnum :
      Tendsto
        (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ (2 ^ (n + 1)))
        atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hp
  have hquot :
      Tendsto
        (fun n : ℕ =>
          (1 - (1 / 2 : ℝ) ^ (2 ^ (n + 1))) /
            (1 - (1 / 2 : ℝ)))
        atTop
        (𝓝 (((1 : ℝ) - 0) / (1 - (1 / 2 : ℝ)))) :=
    hnum.div_const (1 - (1 / 2 : ℝ))
  have hprod :
      Tendsto partialProduct atTop
        (𝓝 (((1 : ℝ) - 0) / (1 - (1 / 2 : ℝ)))) :=
    hquot.congr'
      (Filter.Eventually.of_forall (fun n => (gap4 n).symm))
  simpa using hprod

theorem gap6 : (1 / (1 - (1 / 2 : ℝ))) = 2 := by
  norm_num

theorem gap7 :
    Tendsto partialProduct atTop (𝓝 2) := by
  simpa only [gap6] using gap5

theorem gap8 : HasProduct 2 := by
  simpa [HasProduct] using gap7

theorem gap9 : HasProduct 2 := by
  exact gap8

end

end ProofGap.Exercise3054
