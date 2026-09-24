import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2547

noncomputable section

def term (k : ℕ) : ℝ := 1 / 2 ^ k + 1 / 3 ^ k
def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, term k

theorem gap1 (n : ℕ) : partialSum n = ∑ k ∈ Finset.Icc 1 n, term k := by
  rfl
theorem gap2 (n : ℕ) :
    partialSum n =
      (∑ k ∈ Finset.Icc 1 n, (1 / 2 ^ k : ℝ)) +
      ∑ k ∈ Finset.Icc 1 n, (1 / 3 ^ k : ℝ) := by
  simp only [partialSum, term, Finset.sum_add_distrib]
theorem gap3 (n : ℕ) :
    partialSum n =
      1 / 2 * (1 - 1 / 2 ^ n) / (1 - 1 / 2) +
      1 / 3 * (1 - 1 / 3 ^ n) / (1 - 1 / 3) := by
  induction n with
  | zero =>
      norm_num [partialSum, term]
  | succ n ih =>
      rw [partialSum, Finset.sum_Icc_succ_top (by omega)]
      change partialSum n + term (n + 1) = _
      rw [ih]
      norm_num [term, pow_succ] <;> field_simp <;> ring
theorem gap4 :
    HasSum (fun k : ℕ => term (k + 1)) (3 / 2) ↔
      Filter.Tendsto partialSum Filter.atTop (nhds (3 / 2)) := by
  have h2raw :
      HasSum (fun k : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k)
        ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹) :=
    (hasSum_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (1 / 2 : ℝ)
  have h2 :
      HasSum (fun k : ℕ => 1 / (2 : ℝ) ^ (k + 1)) 1 := by
    convert h2raw using 1
    · funext k
      rw [one_div_pow, pow_succ]
      ring
    · norm_num
  have h3raw :
      HasSum (fun k : ℕ => (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ k)
        ((1 / 3 : ℝ) * (1 - (1 / 3 : ℝ))⁻¹) :=
    (hasSum_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)).mul_left (1 / 3 : ℝ)
  have h3 :
      HasSum (fun k : ℕ => 1 / (3 : ℝ) ^ (k + 1)) (1 / 2) := by
    convert h3raw using 1
    · funext k
      rw [one_div_pow, pow_succ]
      ring
    · norm_num
  have hleft : HasSum (fun k : ℕ => term (k + 1)) (3 / 2) := by
    convert h2.add h3 using 1 <;> norm_num [term]
  have hright :
      Filter.Tendsto partialSum Filter.atTop (nhds (3 / 2)) := by
    have h2lim :
        Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
          Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have h3lim :
        Filter.Tendsto (fun n : ℕ => (1 / 3 : ℝ) ^ n)
          Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)
    have h2lim' :
        Filter.Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n)
          Filter.atTop (nhds 0) := by
      simpa only [one_div_pow] using h2lim
    have h3lim' :
        Filter.Tendsto (fun n : ℕ => 1 / (3 : ℝ) ^ n)
          Filter.atTop (nhds 0) := by
      simpa only [one_div_pow] using h3lim
    have hfirst :
        Filter.Tendsto
          (fun n : ℕ =>
            (1 / 2 : ℝ) * (1 - 1 / 2 ^ n) / (1 - 1 / 2))
          Filter.atTop
          (nhds ((1 / 2 : ℝ) * (1 - 0) / (1 - 1 / 2))) := by
      simpa only [div_eq_mul_inv] using
        (tendsto_const_nhds.mul
          (tendsto_const_nhds.sub h2lim')).mul_const
            ((1 - (1 / 2 : ℝ))⁻¹)
    have hthird :
        Filter.Tendsto
          (fun n : ℕ =>
            (1 / 3 : ℝ) * (1 - 1 / 3 ^ n) / (1 - 1 / 3))
          Filter.atTop
          (nhds ((1 / 3 : ℝ) * (1 - 0) / (1 - 1 / 3))) := by
      simpa only [div_eq_mul_inv] using
        (tendsto_const_nhds.mul
          (tendsto_const_nhds.sub h3lim')).mul_const
            ((1 - (1 / 3 : ℝ))⁻¹)
    rw [show partialSum =
        (fun n : ℕ =>
          (1 / 2 : ℝ) * (1 - 1 / 2 ^ n) / (1 - 1 / 2) +
          (1 / 3 : ℝ) * (1 - 1 / 3 ^ n) / (1 - 1 / 3)) by
      funext n
      exact gap3 n]
    convert hfirst.add hthird using 1 <;> norm_num
  exact ⟨fun _ => hright, fun _ => hleft⟩
theorem gap5 :
    Filter.Tendsto partialSum Filter.atTop
      (nhds (1 / 2 * (1 / (1 - 1 / 2)) +
        1 / 3 * (1 / (1 - 1 / 3)))) := by
  have h2 :
      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h3 :
      Filter.Tendsto (fun n : ℕ => (1 / 3 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)
  have h2' :
      Filter.Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
    simpa only [one_div_pow] using h2
  have h3' :
      Filter.Tendsto (fun n : ℕ => 1 / (3 : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
    simpa only [one_div_pow] using h3
  have hfirst :
      Filter.Tendsto
        (fun n : ℕ =>
          (1 / 2 : ℝ) * (1 - 1 / 2 ^ n) / (1 - 1 / 2))
        Filter.atTop
        (nhds ((1 / 2 : ℝ) * (1 - 0) / (1 - 1 / 2))) := by
    simpa only [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.sub h2')).mul_const
          ((1 - (1 / 2 : ℝ))⁻¹)
  have hthird :
      Filter.Tendsto
        (fun n : ℕ =>
          (1 / 3 : ℝ) * (1 - 1 / 3 ^ n) / (1 - 1 / 3))
        Filter.atTop
        (nhds ((1 / 3 : ℝ) * (1 - 0) / (1 - 1 / 3))) := by
    simpa only [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.sub h3')).mul_const
          ((1 - (1 / 3 : ℝ))⁻¹)
  rw [show partialSum =
      (fun n : ℕ =>
        (1 / 2 : ℝ) * (1 - 1 / 2 ^ n) / (1 - 1 / 2) +
        (1 / 3 : ℝ) * (1 - 1 / 3 ^ n) / (1 - 1 / 3)) by
    funext n
    exact gap3 n]
  simpa only [sub_zero, mul_one, div_eq_mul_inv, one_mul] using
    hfirst.add hthird
theorem gap6 :
    (1 / 2 * (1 / (1 - 1 / 2)) +
      1 / 3 * (1 / (1 - 1 / 3)) : ℝ) = 3 / 2 := by
  norm_num
theorem gap7 : HasSum (fun k : ℕ => term (k + 1)) (3 / 2) := by
  apply gap4.mpr
  rw [← gap6]
  exact gap5

end

end ProofGap.Exercise2547
