import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2549

noncomputable section

def term (k : ℕ) : ℝ := 1 / ((k : ℝ) * (k + 1))
def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, term k

theorem gap1 (n : ℕ) : partialSum n = ∑ k ∈ Finset.Icc 1 n, term k := by
  rfl
theorem gap2 (n : ℕ) :
    partialSum n = ∑ k ∈ Finset.Icc 1 n,
      (1 / (k : ℝ) - 1 / (k + 1 : ℝ)) := by
  unfold partialSum term
  apply Finset.sum_congr rfl
  intro k hk
  have hkposNat : 0 < k := by
    exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hkposNat
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hk1 : (k : ℝ) + 1 ≠ 0 := by
    positivity
  field_simp [hk0, hk1] <;> ring
theorem gap3 (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
      (1 / (k : ℝ) - 1 / (k + 1 : ℝ))) =
      1 - 1 / (n + 1 : ℝ) := by
  cases n with
  | zero => norm_num
  | succ n =>
      induction n with
      | zero => norm_num
      | succ n ih =>
          have hmem : n + 2 ∉ Finset.Icc 1 (n + 1) := by
            simp
          have hfin :
              Finset.Icc 1 (n + 2) =
                insert (n + 2) (Finset.Icc 1 (n + 1)) := by
            ext k
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          rw [hfin, Finset.sum_insert hmem, ih]
          norm_num [Nat.cast_add, Nat.cast_one] <;> ring
theorem gap4 (n : ℕ) : partialSum n = 1 - 1 / (n + 1 : ℝ) := by
  rw [gap2, gap3]
theorem gap5 :
    HasSum (fun k : ℕ => term (k + 1)) 1 ↔
      Filter.Tendsto partialSum Filter.atTop (nhds 1) := by
  have hsum (n : ℕ) :
      (∑ k ∈ Finset.range n, term (k + 1)) = partialSum n := by
    induction n with
    | zero => simp [partialSum]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, gap4 n, gap4 (Nat.succ n)]
        unfold term
        norm_num [Nat.cast_add, Nat.cast_one]
        have h1 : (1 + (n : ℝ)) ≠ 0 := by positivity
        have h2 : (2 + (n : ℝ)) ≠ 0 := by positivity
        field_simp [h1, h2] <;> ring
  have hnonneg : ∀ k : ℕ, 0 ≤ term (k + 1) := by
    intro k
    unfold term
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  simpa only [hsum]
theorem gap6 : Filter.Tendsto partialSum Filter.atTop (nhds 1) := by
  have hzero :
      Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n + 1 : ℝ))
        Filter.atTop (nhds ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hzero
  have hfun :
      partialSum = (fun n : ℕ => (1 : ℝ) - 1 / (n + 1 : ℝ)) := by
    funext n
    exact gap4 n
  rw [hfun]
  simpa only [sub_zero] using hlim
theorem gap7 : HasSum (fun k : ℕ => term (k + 1)) 1 := by
  exact gap5.mpr gap6

end

end ProofGap.Exercise2549
