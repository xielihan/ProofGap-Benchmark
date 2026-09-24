import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2770

noncomputable section

open Filter
open scoped BigOperators

def term (k : ℕ) (x : ℝ) : ℝ :=
  x ^ k / (k : ℝ) - x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)

def partialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, term k x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

private theorem unit_pow_div_bound
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |x| ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ≤
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  have habs : |x| ≤ (1 : ℝ) := (abs_le).2 hx
  have hpow : |x| ^ (n + 1) ≤ (1 : ℝ) :=
    pow_le_one₀ (abs_nonneg x) habs
  have hden : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  exact div_le_div_of_nonneg_right hpow hden

private theorem reciprocal_succ_tendsto :
    Tendsto
      (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto
        (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [Nat.cast_add, Nat.cast_one] using hreal

theorem gap1 (S : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hS : S n x = partialSum n x) :
    S n x = partialSum n x := by
  exact hS

theorem gap2 (n : ℕ) (x : ℝ) :
    partialSum n x = x - x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero =>
      simp [partialSum]
  | succ n ih =>
      have hset :
          Finset.Icc 1 (Nat.succ n) =
            insert (Nat.succ n) (Finset.Icc 1 n) := by
        ext k
        simp
        omega
      have hnot : Nat.succ n ∉ Finset.Icc 1 n := by
        simp
      rw [partialSum, hset, Finset.sum_insert hnot]
      change term (Nat.succ n) x + partialSum n x = _
      rw [ih]
      simp only [term, Nat.succ_eq_add_one]
      ring

theorem gap3 (S : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hS : S n x = partialSum n x) :
    S n x = x - x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  rw [hS, gap2]

theorem gap4 (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Tendsto (fun n => partialSum n x) atTop (nhds x) := by
  have hmajor := reciprocal_succ_tendsto
  have hminor :
      Tendsto
        (fun n : ℕ => -((1 : ℝ) / ((n + 1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    simpa using hmajor.neg
  have htail :
      Tendsto
        (fun n : ℕ => x ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hminor hmajor
    · exact Filter.Eventually.of_forall fun n => by
        have hden : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
        have hb :
            |x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)| ≤
              (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
          calc
            |x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)| =
                |x| ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
                  rw [abs_div, abs_pow, abs_of_nonneg hden]
            _ ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) :=
              unit_pow_div_bound n x hx
        exact (abs_le.mp hb).1
    · exact Filter.Eventually.of_forall fun n => by
        have hden : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
        have hb :
            |x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)| ≤
              (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
          calc
            |x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)| =
                |x| ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
                  rw [abs_div, abs_pow, abs_of_nonneg hden]
            _ ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) :=
              unit_pow_div_bound n x hx
        exact (abs_le.mp hb).2
  simpa [gap2] using (tendsto_const_nhds.sub htail)

theorem gap5 (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |partialSum n x - x| =
      |x| ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  rw [gap2]
  have hden : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      x - x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) - x =
        -(x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    ring
  rw [hdiff, abs_neg, abs_div, abs_pow, abs_of_nonneg hden]

theorem gap6 (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |x| ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ≤
      1 / ((n + 1 : ℕ) : ℝ) := by
  exact unit_pow_div_bound n x hx

theorem gap7 (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self n
  exact one_div_lt_one_div_of_lt hn0 hlt

theorem gap8 (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |partialSum n x - x| < 1 / (n : ℝ) := by
  rw [gap5 n x hx]
  exact lt_of_le_of_lt (gap6 n x hx) (gap7 n hn)

theorem gap9 :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |partialSum n x - x| < ε := by
  intro ε hε
  have ht := reciprocal_succ_tendsto
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < ε :=
    (tendsto_order.1 ht).2 ε hε
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  calc
    |partialSum n x - x| =
        |x| ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := gap5 n x hx
    _ ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := gap6 n x hx
    _ < ε := hN n hn

theorem gap10 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Icc (-1 : ℝ) 1)
      (fun x => x) := by
  have hsum (n : ℕ) (x : ℝ) :
      (∑ k ∈ Finset.range (n + 1), term (k + 1) x) =
        partialSum (n + 1) x := by
    have htel : ∀ m : ℕ,
        (∑ k ∈ Finset.range m, term (k + 1) x) =
          x - x ^ (m + 1) / ((m + 1 : ℕ) : ℝ) := by
      intro m
      induction m with
      | zero =>
          simp [term]
      | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [term, Nat.succ_eq_add_one]
          ring
    rw [htel (n + 1), gap2]
  intro ε hε
  rcases gap9 ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  rw [hsum n x]
  exact hN (n + 1) (by omega) x hx

theorem gap11 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Icc (-1 : ℝ) 1)
      (fun x => x) := by
  exact gap10

end

end ProofGap.Exercise2770
