import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2546

noncomputable section

def term (k : ℕ) : ℝ := (-1 : ℝ) ^ (k - 1) / 2 ^ (k - 1)
def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, term k

private theorem partialSum_eq_sum_range (n : ℕ) :
    partialSum n = Finset.sum (Finset.range n) (fun k => term (k + 1)) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      unfold partialSum
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]

theorem gap1 (n : ℕ) : partialSum n = ∑ k ∈ Finset.Icc 1 n, term k := by
  rfl
theorem gap2 (n : ℕ) :
    partialSum n = (1 - (-1 : ℝ) ^ n / 2 ^ n) / (1 + 1 / 2) := by
  rw [partialSum_eq_sum_range]
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [term, Nat.add_sub_cancel, pow_succ]
      have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hpow]
      ring
theorem gap3 (n : ℕ) :
    partialSum n = (1 - (-1 : ℝ) ^ n / 2 ^ n) / (1 + 1 / 2) := by
  exact gap2 n
theorem gap4 :
    HasSum (fun k : ℕ => term (k + 1)) (2 / 3) ↔
      Filter.Tendsto partialSum Filter.atTop (nhds (2 / 3)) := by
  have hs0 :
      HasSum (fun k : ℕ => (-1 / 2 : ℝ) ^ k) (1 - (-1 / 2 : ℝ))⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have hs1 :
      HasSum (fun k : ℕ => term (k + 1)) (1 - (-1 / 2 : ℝ))⁻¹ := by
    apply hs0.congr
    intro k
    simp [term, div_pow]
  have hs : HasSum (fun k : ℕ => term (k + 1)) (2 / 3) := by
    convert hs1 using 1 <;> norm_num
  constructor
  · intro _
    simpa only [← partialSum_eq_sum_range] using hs.tendsto_sum_nat
  · intro _
    exact hs
theorem gap5 :
    Filter.Tendsto partialSum Filter.atTop (nhds (1 / (1 + 1 / 2))) := by
  have hs0 :
      HasSum (fun k : ℕ => (-1 / 2 : ℝ) ^ k) (1 - (-1 / 2 : ℝ))⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have hs1 :
      HasSum (fun k : ℕ => term (k + 1)) (1 - (-1 / 2 : ℝ))⁻¹ := by
    apply hs0.congr
    intro k
    simp [term, div_pow]
  have hs : HasSum (fun k : ℕ => term (k + 1)) (2 / 3) := by
    convert hs1 using 1 <;> norm_num
  have ht := gap4.mp hs
  convert ht using 1 <;> norm_num
theorem gap6 : (1 / (1 + 1 / 2) : ℝ) = 2 / 3 := by
  norm_num
theorem gap7 : HasSum (fun k : ℕ => term (k + 1)) (2 / 3) := by
  apply gap4.mpr
  rw [← gap6]
  exact gap5
theorem gap8 : Summable (fun k : ℕ => term (k + 1)) := by
  exact gap7.summable

end

end ProofGap.Exercise2546
