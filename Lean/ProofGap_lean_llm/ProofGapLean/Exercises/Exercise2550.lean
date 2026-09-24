import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2550

noncomputable section

def term (k : ℕ) : ℝ :=
  1 / ((3 * k - 2 : ℝ) * (3 * k + 1 : ℝ))
def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, term k

private theorem partialSum_eq_shifted_range (n : ℕ) :
    partialSum n = ∑ k ∈ Finset.range n, term (k + 1) := by
  induction n with
  | zero =>
      simp [partialSum]
  | succ n ih =>
      have hset :
          Finset.Icc 1 (n + 1) =
            insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n + 1 ∉ Finset.Icc 1 n := by
        simp
      rw [partialSum, hset, Finset.sum_insert hnot, ← partialSum, ih,
        Finset.sum_range_succ]
      ac_rfl

theorem gap1 (n : ℕ) : partialSum n = ∑ k ∈ Finset.Icc 1 n, term k := by
  rfl
theorem gap2 (n : ℕ) : partialSum n = ∑ k ∈ Finset.Icc 1 n, term k := by
  exact gap1 n
theorem gap3 (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, term k) =
      1 / 3 * ∑ k ∈ Finset.Icc 1 n,
        (1 / (3 * k - 2 : ℝ) - 1 / (3 * k + 1 : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk1
  have h1 : (3 * k - 2 : ℝ) ≠ 0 := by
    nlinarith
  have h2 : (3 * k + 1 : ℝ) ≠ 0 := by
    nlinarith
  simp only [term]
  field_simp [h1, h2]
  <;> ring
theorem gap4 (n : ℕ) :
    partialSum n =
      1 / 3 * ∑ k ∈ Finset.Icc 1 n,
        (1 / (3 * k - 2 : ℝ) - 1 / (3 * k + 1 : ℝ)) := by
  calc
    partialSum n = ∑ k ∈ Finset.Icc 1 n, term k := gap1 n
    _ = 1 / 3 * ∑ k ∈ Finset.Icc 1 n,
          (1 / (3 * k - 2 : ℝ) - 1 / (3 * k + 1 : ℝ)) := gap3 n
theorem gap5 (n : ℕ) :
    partialSum n = 1 / 3 * (1 - 1 / (3 * n + 1 : ℝ)) := by
  induction n with
  | zero =>
      norm_num [partialSum]
  | succ n ih =>
      have hset :
          Finset.Icc 1 (n + 1) =
            insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n + 1 ∉ Finset.Icc 1 n := by
        simp
      rw [partialSum, hset, Finset.sum_insert hnot, ← partialSum, ih]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have ha : (3 * (n : ℝ) + 1) ≠ 0 := by
        nlinarith
      have hb : (3 * (n : ℝ) + 4) ≠ 0 := by
        nlinarith
      simp only [term, Nat.cast_add, Nat.cast_one]
      have hleft :
          3 * ((n : ℝ) + 1) - 2 = 3 * (n : ℝ) + 1 := by
        ring
      have hright :
          3 * ((n : ℝ) + 1) + 1 = 3 * (n : ℝ) + 4 := by
        ring
      rw [hleft, hright]
      field_simp [ha, hb] <;> ring
theorem gap6 :
    HasSum (fun k : ℕ => term (k + 1)) (1 / 3) ↔
      Filter.Tendsto partialSum Filter.atTop (nhds (1 / 3)) := by
  have hnonneg : ∀ k : ℕ, 0 ≤ term (k + 1) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    simp only [term, Nat.cast_add, Nat.cast_one]
    have hfirst : (0 : ℝ) < 3 * ((k : ℝ) + 1) - 2 := by
      nlinarith
    have hsecond : (0 : ℝ) < 3 * ((k : ℝ) + 1) + 1 := by
      nlinarith
    exact (one_div_pos.mpr (mul_pos hfirst hsecond)).le
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  simpa only [← partialSum_eq_shifted_range]
theorem gap7 : Filter.Tendsto partialSum Filter.atTop (nhds (1 / 3)) := by
  have hden :
      Filter.Tendsto (fun n : ℕ => (3 * n + 1 : ℝ))
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    nlinarith
  have hinv :
      Filter.Tendsto (fun n : ℕ => 1 / (3 * n + 1 : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  have hlim :
      Filter.Tendsto
        (fun n : ℕ => (1 / 3 : ℝ) * (1 - 1 / (3 * n + 1 : ℝ)))
        Filter.atTop (nhds (1 / 3)) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.sub hinv) using 1
    <;> norm_num
  exact hlim.congr' (Filter.Eventually.of_forall (fun n => (gap5 n).symm))
theorem gap8 : HasSum (fun k : ℕ => term (k + 1)) (1 / 3) := by
  exact (gap6).2 gap7

end

end ProofGap.Exercise2550
