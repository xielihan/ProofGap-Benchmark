import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace ProofGap.Exercise2992

noncomputable section

open Filter
open scoped BigOperators

def term (n : ℕ) : ℝ :=
  1 / ((n : ℝ) ^ 2 - 1)

def decomposedTerm (n : ℕ) : ℝ :=
  1 / 2 * (1 / ((n : ℝ) - 1) - 1 / ((n : ℝ) + 1))

def seriesSum : ℝ :=
  ∑' k : ℕ, term (k + 2)

def partialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, term n

def decomposedPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, decomposedTerm n

def closedPartialSum (N : ℕ) : ℝ :=
  1 / 2 *
    (1 + 1 / 2 - 1 / (N + 1 : ℝ) - 1 / (N + 2 : ℝ))

private theorem exercise2992_core :
    HasSum (fun k : ℕ => term (k + 2)) (3 / 4 : ℝ) ∧
      Tendsto partialSum atTop (nhds (3 / 4 : ℝ)) ∧
      Tendsto closedPartialSum atTop (nhds (3 / 4 : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → term n = decomposedTerm n) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hshift : ∀ c : ℝ,
      Tendsto (fun n : ℕ => (n : ℝ) + c) atTop atTop := by
    intro c
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_atTop.1 hnat (b - c))] with n hn
    linarith
  have hinv : ∀ c : ℝ,
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + c)) atTop (nhds 0) := by
    intro c
    simpa only [one_div] using
      ((tendsto_inv_atTop_zero :
          Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp (hshift c))
  have hprefix : ∀ m : ℕ,
      Finset.sum (Finset.range m) (fun k : ℕ => term (k + 2)) =
        (3 / 4 : ℝ) - 1 / 2 *
          (1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 2)) := by
    intro m
    induction m with
    | zero =>
        norm_num
    | succ m ih =>
        have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
        have h3 : (m : ℝ) + 3 ≠ 0 := by positivity
        have ht :
            term (m + 2) =
              1 / 2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 3)) := by
          simp only [term, Nat.cast_add, Nat.cast_ofNat]
          rw [show ((m : ℝ) + 2) ^ 2 - 1 =
              ((m : ℝ) + 1) * ((m : ℝ) + 3) by ring]
          field_simp [h1, h3]
          <;> ring
        rw [Finset.sum_range_succ, ih, ht]
        simp only [Nat.cast_add, Nat.cast_ofNat]
        ring_nf
  have hprefixLim :
      Tendsto
        (fun m : ℕ =>
          (3 / 4 : ℝ) - 1 / 2 *
            (1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 2)))
        atTop (nhds (3 / 4 : ℝ)) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (3 / 4 : ℝ)) atTop (nhds (3 / 4 : ℝ))).sub
        ((tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ))).mul
          ((hinv 1).add (hinv 2))))
  have hnonneg : ∀ k : ℕ, 0 ≤ term (k + 2) := by
    intro k
    have hkNat : 2 ≤ k + 2 := by omega
    have hk : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      exact_mod_cast hkNat
    have hden : 0 < ((k + 2 : ℕ) : ℝ) ^ 2 - 1 := by
      nlinarith
    unfold term
    exact div_nonneg (by norm_num) (le_of_lt hden)
  have hs : HasSum (fun k : ℕ => term (k + 2)) (3 / 4 : ℝ) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
    exact
      (tendsto_congr' (Eventually.of_forall hprefix)).2 hprefixLim
  have hsubtop : Tendsto (fun N : ℕ => N - 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with N hN
    omega
  have hpartialEq : ∀ᶠ N : ℕ in atTop,
      partialSum N =
        (3 / 4 : ℝ) - 1 / 2 *
          (1 / (((N - 1 : ℕ) : ℝ) + 1) +
            1 / (((N - 1 : ℕ) : ℝ) + 2)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hset : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [partialSum, hset, Finset.sum_Ico_eq_sum_range]
    simpa [show N + 1 - 2 = N - 1 by omega, add_comm] using
      hprefix (N - 1)
  have hp : Tendsto partialSum atTop (nhds (3 / 4 : ℝ)) := by
    exact
      (tendsto_congr' hpartialEq).2 (hprefixLim.comp hsubtop)
  have hclosedEq : ∀ N : ℕ,
      closedPartialSum N =
        (3 / 4 : ℝ) - 1 / 2 *
          (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 2)) := by
    intro N
    simp only [closedPartialSum, Nat.cast_add, Nat.cast_ofNat]
    ring_nf
  have hc : Tendsto closedPartialSum atTop (nhds (3 / 4 : ℝ)) := by
    exact
      (tendsto_congr' (Eventually.of_forall hclosedEq)).2 hprefixLim
  have hterm : ∀ n : ℕ, 2 ≤ n → term n = decomposedTerm n := by
    intro n hn
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hminus : (n : ℝ) - 1 ≠ 0 := by
      nlinarith
    have hplus : (n : ℝ) + 1 ≠ 0 := by
      nlinarith
    simp only [term, decomposedTerm]
    rw [show (n : ℝ) ^ 2 - 1 =
        ((n : ℝ) - 1) * ((n : ℝ) + 1) by ring]
    field_simp [hminus, hplus]
    <;> ring
  exact ⟨hs, hp, hc, hterm⟩

theorem gap1 :
    Tendsto partialSum atTop (nhds seriesSum) := by
  have hs := exercise2992_core.1
  have hp := exercise2992_core.2.1
  have hsum : seriesSum = (3 / 4 : ℝ) := by
    simpa [seriesSum] using hs.tsum_eq
  simpa only [hsum] using hp

theorem gap2 :
    ∀ L : ℝ,
      Tendsto partialSum atTop (nhds L) ↔
        Tendsto decomposedPartialSum atTop (nhds L) := by
  intro L
  have hfun : partialSum = decomposedPartialSum := by
    funext N
    unfold partialSum decomposedPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    exact exercise2992_core.2.2.2 n (Finset.mem_Icc.mp hn).1
  rw [hfun]

theorem gap3 :
    ∀ L : ℝ,
      Tendsto decomposedPartialSum atTop (nhds L) ↔
        Tendsto closedPartialSum atTop (nhds L) := by
  intro L
  have hp := exercise2992_core.2.1
  have hc := exercise2992_core.2.2.1
  have hd : Tendsto decomposedPartialSum atTop (nhds (3 / 4 : ℝ)) :=
    (gap2 (3 / 4 : ℝ)).mp hp
  constructor
  · intro h
    have hL : L = (3 / 4 : ℝ) := tendsto_nhds_unique h hd
    simpa only [hL] using hc
  · intro h
    have hL : L = (3 / 4 : ℝ) := tendsto_nhds_unique h hc
    simpa only [hL] using hd

theorem gap4 :
    Tendsto closedPartialSum atTop (nhds seriesSum) := by
  have hs := exercise2992_core.1
  have hc := exercise2992_core.2.2.1
  have hsum : seriesSum = (3 / 4 : ℝ) := by
    simpa [seriesSum] using hs.tsum_eq
  simpa only [hsum] using hc

theorem gap5 :
    seriesSum = 1 / 2 * (1 + 1 / 2) := by
  have hs := exercise2992_core.1
  calc
    seriesSum = (3 / 4 : ℝ) := by
      simpa [seriesSum] using hs.tsum_eq
    _ = 1 / 2 * (1 + 1 / 2) := by norm_num

theorem gap6 :
    (1 / 2 : ℝ) * (1 + 1 / 2) = 3 / 4 := by
  norm_num

theorem gap7 :
    seriesSum = 3 / 4 := by
  exact gap5.trans gap6

end

end ProofGap.Exercise2992
