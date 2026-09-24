import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2660

noncomputable section

open Filter
open scoped BigOperators

def term (n : ℕ) : ℝ :=
  if n % 3 = 0 then -1 / (2 : ℝ) ^ (n - 1)
  else 1 / (2 : ℝ) ^ (n - 1)

def partialSum (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, term n

def geometricFactor (n : ℕ) : ℝ :=
  (1 - (1 / 8 : ℝ) ^ n) / (1 - 1 / 8)

def seriesSum : ℝ :=
  ∑' n : ℕ, term (n + 1)

theorem gap1 :
    Summable (fun n : ℕ => |term (n + 1)|) := by
  have hterm : (fun n : ℕ => |term (n + 1)|) = fun n : ℕ => (1 / 2 : ℝ) ^ n := by
    funext n
    have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    by_cases h : (n + 1) % 3 = 0 <;>
      simp [term, h, abs_div, abs_of_pos hp, div_pow]
  rw [hterm]
  exact summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)

theorem gap2 :
    ∀ n : ℕ,
      partialSum (3 * n) =
        ∑ k ∈ Finset.range n,
          ((1 / (2 : ℝ) ^ (3 * k)) +
            (1 / (2 : ℝ) ^ (3 * k + 1)) -
            (1 / (2 : ℝ) ^ (3 * k + 2))) := by
  intro n
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [show 3 * (n + 1) = 3 * n + 3 by omega]
      rw [partialSum, Finset.sum_Icc_succ_top (by omega : 1 ≤ 3 * n + 3)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 3 * n + 2)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 3 * n + 1)]
      change partialSum (3 * n) + term (3 * n + 1) + term (3 * n + 2) +
          term (3 * n + 3) = _
      rw [ih, Finset.sum_range_succ]
      have h0 : (3 * n + 1) % 3 ≠ 0 := by omega
      have h1 : (3 * n + 2) % 3 ≠ 0 := by omega
      have h2 : (3 * n + 3) % 3 = 0 := by omega
      simp only [term]
      rw [if_neg h0, if_neg h1, if_pos h2]
      rw [show 3 * n + 1 - 1 = 3 * n by omega]
      rw [show 3 * n + 2 - 1 = 3 * n + 1 by omega]
      rw [show 3 * n + 3 - 1 = 3 * n + 2 by omega]
      ring

theorem gap3 :
    ∀ n : ℕ,
      partialSum (3 * n) =
        geometricFactor n + (1 / 2 : ℝ) * geometricFactor n -
          (1 / 4 : ℝ) * geometricFactor n := by
  intro n
  rw [gap2 n]
  have hpow (k : ℕ) : (2 : ℝ) ^ (3 * k) = 8 ^ k := by
    rw [pow_mul]
    norm_num
  have hpow1 (k : ℕ) : (2 : ℝ) ^ (3 * k + 1) = 2 * 8 ^ k := by
    calc
      (2 : ℝ) ^ (3 * k + 1) = 2 ^ (3 * k) * 2 ^ 1 := by rw [pow_add]
      _ = 2 * 8 ^ k := by rw [hpow]; ring
  have hpow2 (k : ℕ) : (2 : ℝ) ^ (3 * k + 2) = 4 * 8 ^ k := by
    calc
      (2 : ℝ) ^ (3 * k + 2) = 2 ^ (3 * k) * 2 ^ 2 := by rw [pow_add]
      _ = 4 * 8 ^ k := by rw [hpow]; ring
  have hblock (k : ℕ) :
      (1 / (2 : ℝ) ^ (3 * k)) +
          (1 / (2 : ℝ) ^ (3 * k + 1)) -
          (1 / (2 : ℝ) ^ (3 * k + 2)) =
        (5 / 4 : ℝ) * (1 / 8 : ℝ) ^ k := by
    rw [hpow, hpow1, hpow2, div_pow]
    simp only [one_pow]
    have h8 : (8 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    field_simp [h8] <;> ring
  have hgeom :
      ∑ k ∈ Finset.range n, (1 / 8 : ℝ) ^ k = geometricFactor n := by
    unfold geometricFactor
    have h := geom_sum_mul (1 / 8 : ℝ) n
    norm_num at h ⊢
    linarith
  calc
    (∑ k ∈ Finset.range n,
        ((1 / (2 : ℝ) ^ (3 * k)) +
          (1 / (2 : ℝ) ^ (3 * k + 1)) -
          (1 / (2 : ℝ) ^ (3 * k + 2)))) =
        ∑ k ∈ Finset.range n, (5 / 4 : ℝ) * (1 / 8 : ℝ) ^ k := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact hblock k
    _ = (5 / 4 : ℝ) * ∑ k ∈ Finset.range n, (1 / 8 : ℝ) ^ k := by
          rw [Finset.mul_sum]
    _ = (5 / 4 : ℝ) * geometricFactor n := by rw [hgeom]
    _ = geometricFactor n + (1 / 2 : ℝ) * geometricFactor n -
          (1 / 4 : ℝ) * geometricFactor n := by ring

theorem gap4 :
    ∀ n : ℕ,
      geometricFactor n + (1 / 2 : ℝ) * geometricFactor n -
          (1 / 4 : ℝ) * geometricFactor n =
        (5 / 4 : ℝ) * geometricFactor n := by
  intro n
  ring

theorem gap5 :
    ∀ n : ℕ,
      partialSum (3 * n) = (5 / 4 : ℝ) * geometricFactor n := by
  intro n
  calc
    partialSum (3 * n) =
        geometricFactor n + (1 / 2 : ℝ) * geometricFactor n -
          (1 / 4 : ℝ) * geometricFactor n := gap3 n
    _ = (5 / 4 : ℝ) * geometricFactor n := gap4 n

theorem gap6 :
    Tendsto (fun n : ℕ => partialSum (3 * n)) atTop (nhds seriesSum) := by
  have hs : Summable (fun n : ℕ => term (n + 1)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using gap1
  have hbase :
      Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, term (k + 1)) atTop
        (nhds seriesSum) := by
    simpa only [seriesSum] using hs.hasSum.tendsto_sum_nat
  have hthree : Tendsto (fun n : ℕ => 3 * n) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact (eventually_ge_atTop b).mono (fun a ha => by omega)
  have hsum : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, term (k + 1)) = partialSum m := by
    intro m
    induction m with
    | zero => simp [partialSum]
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        change (∑ n ∈ Finset.Icc 1 m, term n) + term (m + 1) =
          ∑ n ∈ Finset.Icc 1 (m + 1), term n
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
  simpa only [hsum] using hbase.comp hthree

theorem gap7 :
    Tendsto (fun n : ℕ => partialSum (3 * n)) atTop
      (nhds ((5 / 4 : ℝ) / (1 - 1 / 8))) := by
  have hp : Tendsto (fun n : ℕ => (1 / 8 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hg :
      Tendsto (fun n : ℕ => geometricFactor n) atTop
        (nhds ((1 : ℝ) / (1 - 1 / 8))) := by
    simpa [geometricFactor] using
      (hone.sub hp).div_const (1 - 1 / 8 : ℝ)
  have hc : Tendsto (fun _ : ℕ => (5 / 4 : ℝ)) atTop (nhds (5 / 4 : ℝ)) :=
    tendsto_const_nhds
  simpa only [gap5, div_eq_mul_inv, one_mul] using hc.mul hg

theorem gap8 :
    (5 / 4 : ℝ) / (1 - 1 / 8) = 10 / 7 := by
  norm_num

theorem gap9 :
    seriesSum = 10 / 7 := by
  calc
    seriesSum = (5 / 4 : ℝ) / (1 - 1 / 8) :=
      tendsto_nhds_unique gap6 gap7
    _ = 10 / 7 := gap8

end

end ProofGap.Exercise2660
