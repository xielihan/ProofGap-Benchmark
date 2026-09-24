import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2990

noncomputable section

open Filter
open scoped BigOperators

def term (m n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (n + m : ℝ))

def differenceTerm (m n : ℕ) : ℝ :=
  1 / (m : ℝ) * (1 / (n : ℝ) - 1 / (n + m : ℝ))

def seriesSum (m : ℕ) : ℝ :=
  ∑' k : ℕ, term m (k + 1)

def differenceSeries (m : ℕ) : ℝ :=
  ∑' k : ℕ,
    (1 / (k + 1 : ℝ) - 1 / (k + 1 + m : ℝ))

def partialSum (m N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, term m n

def differencePartialSum (m N : ℕ) : ℝ :=
  1 / (m : ℝ) *
    ∑ n ∈ Finset.Icc 1 N,
      (1 / (n : ℝ) - 1 / (n + m : ℝ))

def harmonic (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, 1 / (k : ℝ)

def tail (m N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, 1 / (N + k : ℝ)

def closedPartialSum (m N : ℕ) : ℝ :=
  1 / (m : ℝ) * (harmonic m - tail m N)

theorem gap1 (m : ℕ) (hm : 1 ≤ m) :
    ∀ n : ℕ, 1 ≤ n → term m n = differenceTerm m n := by
  intro n hn
  unfold term differenceTerm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnm0 : (n + m : ℝ) ≠ 0 := by positivity
  field_simp [hm0, hn0, hnm0]
  ring

theorem gap2 (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (partialSum m) atTop (nhds (seriesSum m)) := by
  have hshift (k : ℕ) :
      Tendsto (fun N : ℕ => N + k) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hinv :
      Tendsto (fun N : ℕ => 1 / (N + 1 : ℝ)) atTop (nhds 0) := by
    have hcast :
        Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (hshift 1)
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  let g : ℕ → ℝ := fun k =>
    1 / (k + 1 : ℝ) - 1 / (k + 2 : ℝ)
  have hg_partial : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, g k) = 1 - 1 / (N + 1 : ℝ) := by
    intro N
    induction N with
    | zero => simp [g]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [g]
        push_cast
        ring
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hg_tendsto :
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, g k)
        atTop (nhds 1) := by
    simpa only [hg_partial, sub_zero] using hone.sub hinv
  have hg_nonneg : ∀ k : ℕ, 0 ≤ g k := by
    intro k
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have hg_eq :
        g k = 1 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
      unfold g
      field_simp [ne_of_gt hk1, ne_of_gt hk2]
      push_cast
      ring
    rw [hg_eq]
    positivity
  have hsum_le_one : ∀ s : Finset ℕ, (∑ k ∈ s, g k) ≤ 1 := by
    intro s
    classical
    by_cases hs : s.Nonempty
    · let K : ℕ := s.max' hs + 1
      have hsub : s ⊆ Finset.range K := by
        intro k hk
        simp only [Finset.mem_range, K]
        exact Nat.lt_succ_of_le (Finset.le_max' s k hk)
      calc
        (∑ k ∈ s, g k) ≤ ∑ k ∈ Finset.range K, g k := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun k _ _ => hg_nonneg k)
        _ = 1 - 1 / (K + 1 : ℝ) := hg_partial K
        _ ≤ 1 := by
          have hnonneg : (0 : ℝ) ≤ 1 / (K + 1 : ℝ) := by positivity
          linarith
    · have hs0 : s = ∅ := by
        ext k
        constructor
        · intro hk
          exact (hs ⟨k, hk⟩).elim
        · intro hk
          simp at hk
      simp [hs0]
  have hg_has : HasSum g 1 := by
    change Tendsto (fun s : Finset ℕ => ∑ k ∈ s, g k)
      atTop (nhds 1)
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      have hevent :
          ∀ᶠ N : ℕ in atTop, a < ∑ k ∈ Finset.range N, g k :=
        (tendsto_order.1 hg_tendsto).1 a ha
      rcases hevent.exists with ⟨N, hN⟩
      filter_upwards [eventually_ge_atTop (Finset.range N)] with s hs
      have hle :
          (∑ k ∈ Finset.range N, g k) ≤ ∑ k ∈ s, g k := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hs
          (fun k _ _ => hg_nonneg k)
      exact lt_of_lt_of_le hN hle
    · intro b hb
      exact Filter.Eventually.of_forall fun s =>
        lt_of_le_of_lt (hsum_le_one s) hb
  have hg : Summable g := hg_has.summable
  have hf_nonneg : ∀ k : ℕ, 0 ≤ term m (k + 1) := by
    intro k
    unfold term
    positivity
  have hfg : ∀ k : ℕ, term m (k + 1) ≤ g k := by
    intro k
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have hg_eq :
        g k = 1 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
      unfold g
      field_simp [ne_of_gt hk1, ne_of_gt hk2]
      push_cast
      ring
    rw [hg_eq]
    have hfacNat : k + 2 ≤ k + 1 + m := by omega
    have hfac :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 1 + m : ℕ) : ℝ) := by
      exact_mod_cast hfacNat
    have hden :
        ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) ≤
          ((k + 1 : ℕ) : ℝ) * ((k + 1 + m : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hfac (le_of_lt hk1)
    have hsmall :
        (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) :=
      mul_pos hk1 hk2
    simpa [term] using one_div_le_one_div_of_le hsmall hden
  have hf : Summable (fun k : ℕ => term m (k + 1)) :=
    Summable.of_nonneg_of_le hf_nonneg hfg hg
  have hseries :
      Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N, term m (k + 1))
        atTop (nhds (∑' k : ℕ, term m (k + 1))) :=
    hf.hasSum.tendsto_sum_nat
  have hsum_succ (f : ℕ → ℝ) (N : ℕ) :
      (∑ n ∈ Finset.Icc 1 (N + 1), f n) =
        (∑ n ∈ Finset.Icc 1 N, f n) + f (N + 1) := by
    have hs :
        Finset.Icc 1 (N + 1) =
          insert (N + 1) (Finset.Icc 1 N) := by
      ext x
      simp
      omega
    rw [hs, Finset.sum_insert (by simp)]
    ring
  have hpartial : ∀ N : ℕ,
      partialSum m N = ∑ k ∈ Finset.range N, term m (k + 1) := by
    intro N
    induction N with
    | zero => simp [partialSum]
    | succ N ih =>
        rw [partialSum, hsum_succ]
        change partialSum m N + term m (N + 1) = _
        rw [ih, Finset.sum_range_succ]
  have hfun :
      partialSum m =
        fun N : ℕ => ∑ k ∈ Finset.range N, term m (k + 1) :=
    funext hpartial
  unfold seriesSum
  rw [hfun]
  exact hseries

theorem gap3 (m : ℕ) (hm : 1 ≤ m) :
    ∀ L : ℝ,
      Tendsto (partialSum m) atTop (nhds L) ↔
        Tendsto (differencePartialSum m) atTop (nhds L) := by
  intro L
  have hEq : ∀ N : ℕ,
      partialSum m N = differencePartialSum m N := by
    intro N
    unfold partialSum differencePartialSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    simpa [differenceTerm] using gap1 m hm n hn1
  have hfun : partialSum m = differencePartialSum m := funext hEq
  rw [hfun]

theorem gap4 (m : ℕ) (hm : 1 ≤ m) :
    seriesSum m = 1 / (m : ℝ) * differenceSeries m := by
  unfold seriesSum differenceSeries
  calc
    (∑' k : ℕ, term m (k + 1)) =
        ∑' k : ℕ,
          (1 / (m : ℝ)) *
            (1 / (k + 1 : ℝ) - 1 / (k + 1 + m : ℝ)) := by
      apply tsum_congr
      intro k
      simpa [differenceTerm] using gap1 m hm (k + 1) (by omega)
    _ = 1 / (m : ℝ) *
        ∑' k : ℕ,
          (1 / (k + 1 : ℝ) - 1 / (k + 1 + m : ℝ)) := by
      rw [tsum_mul_left]

theorem gap5 (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (closedPartialSum m) atTop (nhds (seriesSum m)) := by
  have hsum_succ (f : ℕ → ℝ) (N : ℕ) :
      (∑ n ∈ Finset.Icc 1 (N + 1), f n) =
        (∑ n ∈ Finset.Icc 1 N, f n) + f (N + 1) := by
    have hs :
        Finset.Icc 1 (N + 1) =
          insert (N + 1) (Finset.Icc 1 N) := by
      ext x
      simp
      omega
    rw [hs, Finset.sum_insert (by simp)]
    ring
  have htail_step : ∀ q N : ℕ,
      tail q N - tail q (N + 1) =
        1 / (N + 1 : ℝ) - 1 / (N + 1 + q : ℝ) := by
    intro q
    induction q with
    | zero =>
        intro N
        simp [tail]
    | succ q ih =>
        intro N
        calc
          tail (q + 1) N - tail (q + 1) (N + 1) =
              (tail q N + 1 / (N + (q + 1) : ℝ)) -
                (tail q (N + 1) + 1 / (N + 1 + (q + 1) : ℝ)) := by
            unfold tail
            rw [hsum_succ, hsum_succ]
            push_cast
            ring
          _ = (tail q N - tail q (N + 1)) +
                (1 / (N + (q + 1) : ℝ) -
                  1 / (N + 1 + (q + 1) : ℝ)) := by ring
          _ = (1 / (N + 1 : ℝ) - 1 / (N + 1 + q : ℝ)) +
                (1 / (N + (q + 1) : ℝ) -
                  1 / (N + 1 + (q + 1) : ℝ)) := by rw [ih N]
          _ = 1 / (N + 1 : ℝ) - 1 / (N + 1 + (q + 1) : ℝ) := by
            push_cast
            ring
          _ = 1 / (N + 1 : ℝ) - 1 / (N + 1 + ↑(q + 1) : ℝ) := by
            norm_num [Nat.cast_add]
  have htel : ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        (1 / (n : ℝ) - 1 / (n + m : ℝ))) =
          harmonic m - tail m N := by
    intro N
    induction N with
    | zero => simp [harmonic, tail]
    | succ N ih =>
        rw [hsum_succ, ih]
        have ht := htail_step m N
        push_cast at ht ⊢
        linarith
  have hp : ∀ N : ℕ, partialSum m N = closedPartialSum m N := by
    intro N
    unfold partialSum closedPartialSum
    calc
      (∑ n ∈ Finset.Icc 1 N, term m n) =
          ∑ n ∈ Finset.Icc 1 N,
            (1 / (m : ℝ)) *
              (1 / (n : ℝ) - 1 / (n + m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        simpa [differenceTerm] using gap1 m hm n hn1
      _ = 1 / (m : ℝ) *
          ∑ n ∈ Finset.Icc 1 N,
            (1 / (n : ℝ) - 1 / (n + m : ℝ)) := by
        rw [Finset.mul_sum]
      _ = 1 / (m : ℝ) * (harmonic m - tail m N) := by
        rw [htel]
  have hfun : partialSum m = closedPartialSum m := funext hp
  rw [← hfun]
  exact gap2 m hm

theorem gap6 (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (closedPartialSum m) atTop
      (nhds (1 / (m : ℝ) * harmonic m)) := by
  have hshift (k : ℕ) :
      Tendsto (fun N : ℕ => N + k) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hterm (k : ℕ) :
      Tendsto (fun N : ℕ => 1 / (N + k : ℝ)) atTop (nhds 0) := by
    have hcast :
        Tendsto (fun N : ℕ => ((N + k : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (hshift k)
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hsum : ∀ s : Finset ℕ,
      Tendsto (fun N : ℕ => ∑ k ∈ s, 1 / (N + k : ℝ))
        atTop (nhds 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    | @insert a s ha ih =>
        simpa [Finset.sum_insert, ha] using (hterm a).add ih
  have htail : Tendsto (tail m) atTop (nhds 0) := by
    unfold tail
    exact hsum (Finset.Icc 1 m)
  have hharm :
      Tendsto (fun _ : ℕ => harmonic m) atTop (nhds (harmonic m)) :=
    tendsto_const_nhds
  have hfactor :
      Tendsto (fun _ : ℕ => 1 / (m : ℝ)) atTop
        (nhds (1 / (m : ℝ))) :=
    tendsto_const_nhds
  change Tendsto
    (fun N : ℕ => 1 / (m : ℝ) * (harmonic m - tail m N))
    atTop (nhds (1 / (m : ℝ) * harmonic m))
  simpa only [sub_zero] using hfactor.mul (hharm.sub htail)

theorem gap7 (m : ℕ) (hm : 1 ≤ m) :
    seriesSum m = 1 / (m : ℝ) * harmonic m := by
  exact tendsto_nhds_unique (gap5 m hm) (gap6 m hm)

end

end ProofGap.Exercise2990
