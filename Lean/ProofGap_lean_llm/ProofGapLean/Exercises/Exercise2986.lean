import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2986

noncomputable section

open Filter
open scoped BigOperators

def term (n : ℕ) : ℝ :=
  1 / ((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1))

def decomposedTerm (n : ℕ) : ℝ :=
  1 / 2 * (1 / (2 * (n : ℝ) - 1) - 1 / (2 * (n : ℝ) + 1))

def seriesSum : ℝ :=
  ∑' k : ℕ, term (k + 1)

def partialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, term n

def decomposedPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, decomposedTerm n

def closedPartialSum (N : ℕ) : ℝ :=
  1 / 2 - 1 / 2 * (1 / (2 * (N : ℝ) + 1))

private theorem term_eq_decomposed_of_one_le (n : ℕ) (hn : 1 ≤ n) :
    term n = decomposedTerm n := by
  unfold term decomposedTerm
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hminus : 2 * (n : ℝ) - 1 ≠ 0 := by
    nlinarith
  have hplus : 2 * (n : ℝ) + 1 ≠ 0 := by
    nlinarith
  field_simp [hminus, hplus] <;> ring

private theorem rangeSum_eq_closedPartialSum (N : ℕ) :
    (∑ k ∈ Finset.range N, term (k + 1)) = closedPartialSum N := by
  induction N with
  | zero =>
      norm_num [closedPartialSum]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih,
        term_eq_decomposed_of_one_le (N + 1) (by omega)]
      unfold decomposedTerm closedPartialSum
      norm_num [Nat.cast_add, Nat.cast_one] <;> ring

private theorem partialSum_eq_rangeSum (N : ℕ) :
    partialSum N = ∑ k ∈ Finset.range N, term (k + 1) := by
  unfold partialSum
  refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
  · intro n hn
    apply Finset.mem_range.mpr
    change n - 1 < N
    have hnIcc := Finset.mem_Icc.mp hn
    omega
  · intro a ha b hb hab
    change a - 1 = b - 1 at hab
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    calc
      a = a - 1 + 1 := (Nat.sub_add_cancel ha1).symm
      _ = b - 1 + 1 := congrArg (fun x => x + 1) hab
      _ = b := Nat.sub_add_cancel hb1
  · intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    change k + 1 - 1 = k
    omega
  · intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    change term a = term (a - 1 + 1)
    rw [Nat.sub_add_cancel ha1]

private theorem partialSum_eq_decomposedPartialSum (N : ℕ) :
    partialSum N = decomposedPartialSum N := by
  unfold partialSum decomposedPartialSum
  apply Finset.sum_congr rfl
  intro n hn
  exact term_eq_decomposed_of_one_le n (Finset.mem_Icc.mp hn).1

private theorem decomposedPartialSum_eq_closedPartialSum (N : ℕ) :
    decomposedPartialSum N = closedPartialSum N := by
  calc
    decomposedPartialSum N = partialSum N :=
      (partialSum_eq_decomposedPartialSum N).symm
    _ = ∑ k ∈ Finset.range N, term (k + 1) := partialSum_eq_rangeSum N
    _ = closedPartialSum N := rangeSum_eq_closedPartialSum N

private theorem closedPartialSum_tendsto :
    Tendsto closedPartialSum atTop (nhds (1 / 2 : ℝ)) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden :
      Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [tendsto_atTop.1 hnat b] with N hN
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hinv :
      Tendsto (fun N : ℕ => (2 * (N : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hconst :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hprod :
      Tendsto (fun N : ℕ => (1 / 2 : ℝ) * (2 * (N : ℝ) + 1)⁻¹)
        atTop (nhds 0) := by
    simpa using hconst.mul hinv
  change Tendsto
    (fun N : ℕ =>
      (1 / 2 : ℝ) - 1 / 2 * (1 / (2 * (N : ℝ) + 1)))
    atTop (nhds (1 / 2 : ℝ))
  simpa [one_div] using hconst.sub hprod

private theorem shiftedTerm_nonneg (k : ℕ) : 0 ≤ term (k + 1) := by
  unfold term
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hminus : 0 < 2 * ((k + 1 : ℕ) : ℝ) - 1 := by
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hplus : 0 < 2 * ((k + 1 : ℕ) : ℝ) + 1 := by
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith
  exact div_nonneg (by norm_num) (mul_nonneg hminus.le hplus.le)

private theorem shiftedTerm_hasSum :
    HasSum (fun k : ℕ => term (k + 1)) (1 / 2 : ℝ) := by
  exact (hasSum_iff_tendsto_nat_of_nonneg
    (fun k : ℕ => shiftedTerm_nonneg k) (1 / 2 : ℝ)).2
    (closedPartialSum_tendsto.congr'
      (Eventually.of_forall fun N => (rangeSum_eq_closedPartialSum N).symm))

private theorem seriesSum_eq_half : seriesSum = (1 / 2 : ℝ) := by
  unfold seriesSum
  exact shiftedTerm_hasSum.tsum_eq

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → term n = decomposedTerm n := by
  intro n hn
  exact term_eq_decomposed_of_one_le n hn

theorem gap2 :
    Tendsto partialSum atTop (nhds seriesSum) := by
  rw [seriesSum_eq_half]
  exact closedPartialSum_tendsto.congr'
    (Eventually.of_forall fun N =>
      ((partialSum_eq_rangeSum N).trans (rangeSum_eq_closedPartialSum N)).symm)

theorem gap3 :
    ∀ L : ℝ,
      Tendsto partialSum atTop (nhds L) ↔
        Tendsto decomposedPartialSum atTop (nhds L) := by
  intro L
  constructor
  · intro h
    exact h.congr'
      (Eventually.of_forall fun N => partialSum_eq_decomposedPartialSum N)
  · intro h
    exact h.congr'
      (Eventually.of_forall fun N => (partialSum_eq_decomposedPartialSum N).symm)

theorem gap4 :
    ∀ L : ℝ,
      Tendsto decomposedPartialSum atTop (nhds L) ↔
        Tendsto closedPartialSum atTop (nhds L) := by
  intro L
  constructor
  · intro h
    exact h.congr'
      (Eventually.of_forall fun N => decomposedPartialSum_eq_closedPartialSum N)
  · intro h
    exact h.congr'
      (Eventually.of_forall fun N => (decomposedPartialSum_eq_closedPartialSum N).symm)

theorem gap5 :
    Tendsto closedPartialSum atTop (nhds (1 / 2 : ℝ)) := by
  exact closedPartialSum_tendsto

theorem gap6 :
    seriesSum = 1 / 2 := by
  exact seriesSum_eq_half

end

end ProofGap.Exercise2986
