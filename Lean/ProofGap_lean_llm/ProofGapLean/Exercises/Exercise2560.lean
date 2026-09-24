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

namespace ProofGap.Exercise2560

noncomputable section

def comparisonTerm (n : ℕ) : ℝ := 1 / (1001 * (n : ℝ))
def targetTerm (n : ℕ) : ℝ := 1 / (1000 * (n : ℝ) + 1)

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → targetTerm n ≥ comparisonTerm n := by
  intro n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  unfold targetTerm comparisonTerm
  have hden1 : 0 < 1001 * (n : ℝ) := by positivity
  have hden2 : 0 < 1000 * (n : ℝ) + 1 := by positivity
  apply (div_le_div_iff₀ hden1 hden2).2
  nlinarith

theorem gap2
    (hcompare : ∀ n : ℕ, 1 ≤ n → targetTerm n ≥ comparisonTerm n) :
    ¬ Summable comparisonTerm := by
  intro hs
  obtain ⟨s, hs⟩ := hs
  have hpartial :
      Tendsto
        (fun n : ℕ => Finset.sum (Finset.range n) comparisonTerm)
        atTop (nhds s) :=
    hs.tendsto_sum_nat
  have hcauchy :
      CauchySeq
        (fun n : ℕ => Finset.sum (Finset.range n) comparisonTerm) :=
    hpartial.cauchySeq
  obtain ⟨N, hN⟩ :=
    (Metric.cauchySeq_iff.1 hcauchy) ((1 : ℝ) / 2002) (by norm_num)
  have hblock (n : ℕ) (hn : 1 ≤ n) :
      (1 : ℝ) / 2002 ≤
        Finset.sum (Finset.range (n + n)) comparisonTerm -
          Finset.sum (Finset.range n) comparisonTerm := by
    rw [Finset.sum_range_add, add_sub_cancel_left]
    have hnpos_nat : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hnpos_nat
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    calc
      (1 : ℝ) / 2002 =
          Finset.sum (Finset.range n)
            (fun _k => (1 / (2002 * (n : ℝ)) : ℝ)) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              field_simp [hn0] <;> ring
      _ ≤ Finset.sum (Finset.range n)
            (fun k => comparisonTerm (n + k)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : (k : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hk)
        have hnkpos_nat : 0 < n + k := by omega
        have hnkpos : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by
          exact_mod_cast hnkpos_nat
        have hdenBig : 0 < (2002 : ℝ) * (n : ℝ) :=
          mul_pos (by norm_num) hnpos
        have hdenSmall : 0 < (1001 : ℝ) * ((n + k : ℕ) : ℝ) :=
          mul_pos (by norm_num) hnkpos
        unfold comparisonTerm
        apply (div_le_div_iff₀ hdenBig hdenSmall).2
        norm_num [Nat.cast_add]
        nlinarith [hk']
  let n : ℕ := N + 1
  have hn : 1 ≤ n := by
    simp [n]
  have hnN : N ≤ n := by
    simp [n]
  have h2nN : N ≤ n + n := by
    omega
  have hclose :
      dist
          (Finset.sum (Finset.range (n + n)) comparisonTerm)
          (Finset.sum (Finset.range n) comparisonTerm) <
        (1 : ℝ) / 2002 :=
    hN (n + n) h2nN n hnN
  have hsmall :
      Finset.sum (Finset.range (n + n)) comparisonTerm -
          Finset.sum (Finset.range n) comparisonTerm <
        (1 : ℝ) / 2002 := by
    have habs :
        |Finset.sum (Finset.range (n + n)) comparisonTerm -
          Finset.sum (Finset.range n) comparisonTerm| <
            (1 : ℝ) / 2002 := by
      simpa only [Real.dist_eq] using hclose
    exact lt_of_le_of_lt (le_abs_self _) habs
  exact (not_lt_of_ge (hblock n hn)) hsmall

theorem gap3
    (hcompare : ∀ n : ℕ, 1 ≤ n → targetTerm n ≥ comparisonTerm n)
    (hdiv : ¬ Summable comparisonTerm) :
    ¬ Summable targetTerm := by
  intro ht
  apply hdiv
  refine ht.of_norm_bounded ?_
  intro n
  have hnonneg : 0 ≤ comparisonTerm n := by
    unfold comparisonTerm
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  by_cases hn : n = 0
  · subst n
    norm_num [comparisonTerm, targetTerm]
  · exact hcompare n (Nat.one_le_iff_ne_zero.mpr hn)

end

end ProofGap.Exercise2560
