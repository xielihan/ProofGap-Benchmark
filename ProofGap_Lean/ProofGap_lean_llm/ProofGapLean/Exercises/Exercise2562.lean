import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2562

noncomputable section

def oddSquareTerm (n : ℕ) : ℝ := 1 / (2 * (n : ℝ) - 1) ^ 2
def squareTerm (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

private theorem reciprocalSquareSummable :
    Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  simpa using (Real.summable_nat_pow_inv 0)

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → 0 < oddSquareTerm n := by
  intro n hn
  unfold oddSquareTerm
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hbase : 0 < 2 * (n : ℝ) - 1 := by
    linarith
  exact one_div_pos.mpr (pow_pos hbase 2)

theorem gap2
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < oddSquareTerm n) :
    ∀ n : ℕ, 1 ≤ n → oddSquareTerm n ≤ squareTerm n := by
  intro n hn
  unfold oddSquareTerm squareTerm
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hbase : 0 < 2 * (n : ℝ) - 1 := by
    linarith
  have hle : (n : ℝ) ≤ 2 * (n : ℝ) - 1 := by
    linarith
  have hsq : (n : ℝ) ^ 2 ≤ (2 * (n : ℝ) - 1) ^ 2 := by
    nlinarith
  exact one_div_le_one_div_of_le (pow_pos hnPos 2) hsq

theorem gap3
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < oddSquareTerm n)
    (hcompare : ∀ n : ℕ, 1 ≤ n → oddSquareTerm n ≤ squareTerm n) :
    ∀ n : ℕ, 1 ≤ n → 0 < squareTerm n := by
  intro n hn
  exact lt_of_lt_of_le (hpos n hn) (hcompare n hn)

theorem gap4
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < oddSquareTerm n)
    (hcompare : ∀ n : ℕ, 1 ≤ n → oddSquareTerm n ≤ squareTerm n)
    (hsquarePos : ∀ n : ℕ, 1 ≤ n → 0 < squareTerm n) :
    Summable squareTerm := by
  change Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2)
  simpa only [one_div] using reciprocalSquareSummable

theorem gap5
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < oddSquareTerm n)
    (hcompare : ∀ n : ℕ, 1 ≤ n → oddSquareTerm n ≤ squareTerm n)
    (hsquarePos : ∀ n : ℕ, 1 ≤ n → 0 < squareTerm n)
    (hsquare : Summable squareTerm) :
    Summable oddSquareTerm := by
  refine hsquare.of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  simpa [Real.norm_eq_abs, abs_of_pos (hpos n hn)] using hcompare n hn

end

end ProofGap.Exercise2562
