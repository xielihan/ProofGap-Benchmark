import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3058

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (x : ℝ) (n : ℕ) : ℝ :=
  1 + x ^ (2 ^ n)

def partialProduct (x : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range (n + 1), factor x i

def HasProduct (x L : ℝ) : Prop :=
  Tendsto (partialProduct x) atTop (𝓝 L)

theorem gap1 (x : ℝ) (n : ℕ) :
    (1 - x) * partialProduct x n =
      (1 - x) *
        ∏ i ∈ Finset.range (n + 1), (1 + x ^ (2 ^ i)) := by
  rfl

theorem gap2 (x : ℝ) (n : ℕ) :
    (1 - x) *
        (∏ i ∈ Finset.range (n + 1), (1 + x ^ (2 ^ i))) =
      1 - x ^ (2 ^ (n + 1)) := by
  induction n with
  | zero =>
      simp [Finset.prod_range_succ]
      <;> ring
  | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih]
      have hpow :
          x ^ (2 ^ ((n + 1) + 1)) =
            (x ^ (2 ^ (n + 1))) ^ 2 := by
        rw [pow_succ, pow_mul]
      rw [hpow]
      ring

theorem gap3 (x : ℝ) (n : ℕ) :
    (1 - x) * partialProduct x n =
      1 - x ^ (2 ^ (n + 1)) := by
  calc
    (1 - x) * partialProduct x n =
        (1 - x) *
          ∏ i ∈ Finset.range (n + 1), (1 + x ^ (2 ^ i)) := gap1 x n
    _ = 1 - x ^ (2 ^ (n + 1)) := gap2 x n

theorem gap4 (x : ℝ) (n : ℕ) (hx : x ≠ 1) :
    partialProduct x n =
      (1 - x ^ (2 ^ (n + 1))) / (1 - x) := by
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hx))).2
  simpa [mul_comm] using gap3 x n

theorem gap5 (x : ℝ) (hx : |x| < 1) :
    Tendsto (partialProduct x) atTop (𝓝 (1 / (1 - x))) := by
  have hx1 : x ≠ 1 :=
    ne_of_lt (lt_of_le_of_lt (le_abs_self x) hx)
  have hbound : ∀ n : ℕ, n + 1 ≤ (2 : ℕ) ^ (n + 1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        change n + 2 ≤ (2 : ℕ) ^ (n + 2)
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        omega
  have hidx :
      Tendsto (fun n : ℕ => (2 : ℕ) ^ (n + 1)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans ((Nat.le_succ n).trans (hbound n))
  have hpow :
      Tendsto (fun n : ℕ => x ^ (2 ^ (n + 1))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx).comp hidx
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  rw [show partialProduct x =
      (fun n : ℕ => (1 - x ^ (2 ^ (n + 1))) / (1 - x)) by
        funext n
        exact gap4 x n hx1]
  simpa using (hone.sub hpow).div_const (1 - x)

theorem gap6 (x : ℝ) (hx : |x| < 1) :
    HasProduct x (1 / (1 - x)) := by
  simpa [HasProduct] using gap5 x hx

theorem gap7 :
    HasProduct (1 / 2 : ℝ) (1 / (1 - (1 / 2 : ℝ))) := by
  apply gap6
  norm_num [abs_of_nonneg]

theorem gap8 : (1 / (1 - (1 / 2 : ℝ))) = 2 := by
  norm_num

theorem gap9 : HasProduct (1 / 2 : ℝ) 2 := by
  simpa only [gap8] using gap7

theorem gap10 (x : ℝ) (hx : |x| < 1) :
    HasProduct x (1 / (1 - x)) := by
  exact gap6 x hx

end

end ProofGap.Exercise3058
