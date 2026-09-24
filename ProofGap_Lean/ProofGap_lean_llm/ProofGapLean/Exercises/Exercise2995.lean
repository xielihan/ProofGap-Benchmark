import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2995

noncomputable section

open Filter
open scoped BigOperators

def term (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / (Nat.factorial n : ℝ)

def seriesSum : ℝ :=
  ∑' k : ℕ, term (k + 1)

def partialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, term n

def splitInitialPartial (N : ℕ) : ℝ :=
  1 + 2 + ∑ n ∈ Finset.Icc 3 N, term n

def factorialDecompositionPartial (N : ℕ) : ℝ :=
  3 + ∑ n ∈ Finset.Icc 3 N,
    (1 / (Nat.factorial (n - 1) : ℝ) +
      1 / (Nat.factorial (n - 2) : ℝ))

def reindexedPartial (N : ℕ) : ℝ :=
  3 +
    (∑ k ∈ Finset.Icc 2 (N - 1),
      1 / (Nat.factorial k : ℝ)) +
    ∑ l ∈ Finset.Icc 1 (N - 2),
      1 / (Nat.factorial l : ℝ)

def exponentialPartial (N : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (N + 1), 1 / (Nat.factorial s : ℝ)

def errorTerm (N : ℕ) : ℝ :=
  -(1 / (Nat.factorial (N - 1) : ℝ)) -
    2 / (Nat.factorial N : ℝ)

def approximation (N : ℕ) : ℝ :=
  2 * exponentialPartial N + errorTerm N

private def invFactorial (n : ℕ) : ℝ :=
  1 / (Nat.factorial n : ℝ)

private def weightedFactorial (n : ℕ) : ℝ :=
  (n : ℝ) / (Nat.factorial n : ℝ)

private theorem hasSum_invFactorial :
    HasSum invFactorial (Real.exp 1) := by
  rw [Real.exp_eq_exp_ℝ]
  change HasSum (fun n : ℕ => 1 / (Nat.factorial n : ℝ))
    (NormedSpace.exp (1 : ℝ))
  simpa [div_eq_mul_inv] using
    (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (x := (1 : ℝ)))

private theorem weightedFactorial_succ (n : ℕ) :
    weightedFactorial (n + 1) = invFactorial n := by
  simp only [weightedFactorial, invFactorial, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hn, hf]

private theorem term_succ_decomposition (n : ℕ) :
    term (n + 1) = invFactorial n + weightedFactorial n := by
  simp only [term, invFactorial, weightedFactorial, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hn, hf]
  ring

private theorem summable_weightedFactorial :
    Summable weightedFactorial := by
  have ht : Summable (fun n : ℕ => weightedFactorial (n + 1)) := by
    simpa only [weightedFactorial_succ] using hasSum_invFactorial.summable
  exact (summable_nat_add_iff 1).mp ht

private theorem tsum_weightedFactorial :
    ∑' n : ℕ, weightedFactorial n = Real.exp 1 := by
  have hsplit := summable_weightedFactorial.sum_add_tsum_nat_add 1
  calc
    (∑' n : ℕ, weightedFactorial n) =
        (∑ n ∈ Finset.range 1, weightedFactorial n) +
          ∑' n : ℕ, weightedFactorial (n + 1) := by
            simpa using hsplit.symm
    _ = ∑' n : ℕ, invFactorial n := by
          rw [show (∑ n ∈ Finset.range 1, weightedFactorial n) = 0 by
            simp [weightedFactorial]]
          simp only [zero_add]
          apply tsum_congr
          intro n
          exact weightedFactorial_succ n
    _ = Real.exp 1 := hasSum_invFactorial.tsum_eq

private theorem summable_term :
    Summable term := by
  have ht : Summable (fun n : ℕ => term (n + 1)) := by
    have h := hasSum_invFactorial.summable.add summable_weightedFactorial
    simpa only [term_succ_decomposition] using h
  exact (summable_nat_add_iff 1).mp ht

private theorem hasSum_term :
    HasSum term seriesSum := by
  have hsplit := summable_term.sum_add_tsum_nat_add 1
  have htsum : (∑' n : ℕ, term n) = seriesSum := by
    calc
      (∑' n : ℕ, term n) =
          (∑ n ∈ Finset.range 1, term n) +
            ∑' n : ℕ, term (n + 1) := by
              simpa using hsplit.symm
      _ = seriesSum := by
            rw [show (∑ n ∈ Finset.range 1, term n) = 0 by
              norm_num [term, Finset.sum_range_succ, Nat.factorial]]
            simp [seriesSum]
  rw [← htsum]
  exact summable_term.hasSum

private theorem seriesSum_eq_two_exp :
    seriesSum = 2 * Real.exp 1 := by
  unfold seriesSum
  have h := hasSum_invFactorial.add summable_weightedFactorial.hasSum
  have hs : HasSum (fun n : ℕ => term (n + 1))
      (Real.exp 1 + ∑' n : ℕ, weightedFactorial n) := by
    simpa only [term_succ_decomposition] using h
  rw [hs.tsum_eq, tsum_weightedFactorial]
  ring

private theorem tendsto_nat_succ_atTop :
    Tendsto (fun n : ℕ => n + 1) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with a ha
  omega

private theorem tendsto_nat_sub_atTop (d : ℕ) :
    Tendsto (fun n : ℕ => n - d) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (b + d)] with a ha
  omega

private theorem tendsto_Icc_sum {f : ℕ → ℝ} {s : ℝ}
    (hf : HasSum f s) (m : ℕ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc m N, f n) atTop
      (nhds (s - ∑ n ∈ Finset.range m, f n)) := by
  have ht := hf.tendsto_sum_nat.comp tendsto_nat_succ_atTop
  have hc : Tendsto
      (fun _ : ℕ => ∑ n ∈ Finset.range m, f n) atTop
      (nhds (∑ n ∈ Finset.range m, f n)) := tendsto_const_nhds
  have hdiff := ht.sub hc
  have heq :
      (fun N : ℕ => ∑ n ∈ Finset.Icc m N, f n) =ᶠ[atTop]
        (fun N : ℕ =>
          (∑ n ∈ Finset.range (N + 1), f n) -
            ∑ n ∈ Finset.range m, f n) := by
    filter_upwards [eventually_ge_atTop m] with N hN
    have hi : Finset.Icc m N = Finset.Ico m (N + 1) := by
      ext n
      simp
    have hu : Finset.range (N + 1) =
        Finset.range m ∪ Finset.Ico m (N + 1) := by
      ext n
      simp
      omega
    have hd : Disjoint (Finset.range m) (Finset.Ico m (N + 1)) := by
      refine Finset.disjoint_left.2 ?_
      intro n hn hm
      simp at hn hm
      omega
    rw [hi, hu, Finset.sum_union hd]
    ring
  exact (tendsto_congr' heq).2 hdiff

private theorem tendsto_splitInitial :
    Tendsto splitInitialPartial atTop (nhds seriesSum) := by
  have h := tendsto_Icc_sum hasSum_term 3
  have hc : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) :=
    tendsto_const_nhds
  have hinit : (∑ n ∈ Finset.range 3, term n) = 3 := by
    norm_num [term, Finset.sum_range_succ, Nat.factorial]
  convert hc.add h using 1
  · funext N
    norm_num [splitInitialPartial]
  · rw [hinit]
    ring

private theorem term_factorial_decomposition (n : ℕ) (hn : 3 ≤ n) :
    term n =
      1 / (Nat.factorial (n - 1) : ℝ) +
        1 / (Nat.factorial (n - 2) : ℝ) := by
  let k := n - 2
  have hnk : n = k + 2 := by
    dsimp [k]
    omega
  rw [hnk]
  have hsub1 : k + 2 - 1 = k + 1 := by omega
  have hsub2 : k + 2 - 2 = k := by omega
  rw [hsub1, hsub2]
  have hfac : Nat.factorial (k + 2) =
      (k + 2) * (k + 1) * Nat.factorial k := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ,
      Nat.factorial_succ]
    ring
  simp only [term]
  rw [hfac, Nat.factorial_succ]
  norm_num [Nat.cast_mul]
  field_simp [Nat.factorial_ne_zero]
  ring

private theorem splitInitial_eq_factorial (N : ℕ) :
    splitInitialPartial N = factorialDecompositionPartial N := by
  calc
    splitInitialPartial N =
        3 + ∑ n ∈ Finset.Icc 3 N, term n := by
          unfold splitInitialPartial
          norm_num
    _ = 3 + ∑ n ∈ Finset.Icc 3 N,
          (1 / (Nat.factorial (n - 1) : ℝ) +
            1 / (Nat.factorial (n - 2) : ℝ)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          exact term_factorial_decomposition n (Finset.mem_Icc.mp hn).1
    _ = factorialDecompositionPartial N := rfl

private theorem tendsto_reindexed :
    Tendsto reindexedPartial atTop (nhds (2 * Real.exp 1)) := by
  have hfirstBase := tendsto_Icc_sum hasSum_invFactorial 2
  have hsecondBase := tendsto_Icc_sum hasSum_invFactorial 1
  have hfirst := hfirstBase.comp (tendsto_nat_sub_atTop 1)
  have hsecond := hsecondBase.comp (tendsto_nat_sub_atTop 2)
  have hc : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) :=
    tendsto_const_nhds
  have hinit2 : (∑ n ∈ Finset.range 2, invFactorial n) = 2 := by
    norm_num [invFactorial, Finset.sum_range_succ, Nat.factorial]
  have hinit1 : (∑ n ∈ Finset.range 1, invFactorial n) = 1 := by
    norm_num [invFactorial, Finset.sum_range_succ, Nat.factorial]
  have hlim :
      3 + (Real.exp 1 - ∑ n ∈ Finset.range 2, invFactorial n) +
          (Real.exp 1 - ∑ n ∈ Finset.range 1, invFactorial n) =
        2 * Real.exp 1 := by
    rw [hinit2, hinit1]
    ring
  rw [← hlim]
  simpa only [reindexedPartial, invFactorial, Function.comp_apply] using
    (hc.add hfirst).add hsecond

private theorem tendsto_exponentialPartial :
    Tendsto exponentialPartial atTop (nhds (Real.exp 1)) := by
  have h := hasSum_invFactorial.tendsto_sum_nat.comp tendsto_nat_succ_atTop
  simpa only [exponentialPartial, invFactorial, Function.comp_apply] using h

private theorem tendsto_errorTerm :
    Tendsto errorTerm atTop (nhds 0) := by
  have hz : Tendsto invFactorial atTop (nhds 0) :=
    hasSum_invFactorial.summable.tendsto_atTop_zero
  have hp := hz.comp (tendsto_nat_sub_atTop 1)
  have hc : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hm := hc.mul hz
  convert hp.neg.sub hm using 1
  · funext N
    simp only [Function.comp_apply]
    unfold errorTerm invFactorial
    ring
  · ring

private theorem tendsto_approximation :
    Tendsto approximation atTop (nhds (2 * Real.exp 1)) := by
  have hc : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  simpa [approximation] using
    (hc.mul tendsto_exponentialPartial).add tendsto_errorTerm

theorem gap1 :
    Tendsto partialSum atTop (nhds seriesSum) := by
  have h := tendsto_Icc_sum hasSum_term 1
  simpa [partialSum, term] using h

theorem gap2 :
    ∀ L : ℝ,
      Tendsto partialSum atTop (nhds L) ↔
        Tendsto splitInitialPartial atTop (nhds L) := by
  intro L
  constructor
  · intro hL
    have hLS : L = seriesSum := tendsto_nhds_unique hL gap1
    simpa [hLS] using tendsto_splitInitial
  · intro hL
    have hLS : L = seriesSum := tendsto_nhds_unique hL tendsto_splitInitial
    simpa [hLS] using gap1

theorem gap3 :
    Tendsto splitInitialPartial atTop (nhds seriesSum) := by
  exact tendsto_splitInitial

theorem gap4 :
    Tendsto factorialDecompositionPartial atTop (nhds seriesSum) := by
  have heq : splitInitialPartial =ᶠ[atTop] factorialDecompositionPartial :=
    Filter.Eventually.of_forall splitInitial_eq_factorial
  exact (tendsto_congr' heq).1 gap3

theorem gap5 :
    Tendsto reindexedPartial atTop (nhds seriesSum) := by
  rw [seriesSum_eq_two_exp]
  exact tendsto_reindexed

theorem gap6 :
    ∀ L : ℝ,
      Tendsto reindexedPartial atTop (nhds L) ↔
        Tendsto approximation atTop (nhds L) := by
  intro L
  constructor
  · intro hL
    have hLE : L = 2 * Real.exp 1 := tendsto_nhds_unique hL tendsto_reindexed
    simpa [hLE] using tendsto_approximation
  · intro hL
    have hLE : L = 2 * Real.exp 1 := tendsto_nhds_unique hL tendsto_approximation
    simpa [hLE] using tendsto_reindexed

theorem gap7 :
    Tendsto approximation atTop (nhds (2 * Real.exp 1)) := by
  exact tendsto_approximation

theorem gap8 :
    seriesSum = 2 * Real.exp 1 := by
  exact seriesSum_eq_two_exp

end

end ProofGap.Exercise2995
