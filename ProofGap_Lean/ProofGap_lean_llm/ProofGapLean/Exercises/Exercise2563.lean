import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2563

noncomputable section

def rootTerm (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.sqrt ((n : ℝ) + 1))

def threeHalvesTerm (n : ℕ) : ℝ :=
  1 / Real.rpow (n : ℝ) (3 / 2 : ℝ)

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → 0 < rootTerm n := by
  intro n hn
  unfold rootTerm
  positivity

theorem gap2
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < rootTerm n) :
    ∀ n : ℕ, 1 ≤ n → rootTerm n < threeHalvesTerm n := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hsqrt : Real.sqrt (n : ℝ) < Real.sqrt ((n : ℝ) + 1) := by
    exact Real.sqrt_lt_sqrt (le_of_lt hnpos) (by linarith)
  have hdenom :
      Real.rpow (n : ℝ) (3 / 2 : ℝ) < (n : ℝ) * Real.sqrt ((n : ℝ) + 1) := by
    change (n : ℝ) ^ (3 / 2 : ℝ) < (n : ℝ) * Real.sqrt ((n : ℝ) + 1)
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hnpos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    exact mul_lt_mul_of_pos_left hsqrt hnpos
  unfold rootTerm threeHalvesTerm
  exact one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos hnpos _) hdenom

theorem gap3
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < rootTerm n)
    (hcompare : ∀ n : ℕ, 1 ≤ n → rootTerm n < threeHalvesTerm n) :
    ∀ n : ℕ, 1 ≤ n → 0 < threeHalvesTerm n := by
  intro n hn
  exact (hpos n hn).trans (hcompare n hn)

theorem gap4
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < rootTerm n)
    (hcompare : ∀ n : ℕ, 1 ≤ n → rootTerm n < threeHalvesTerm n)
    (hpowerPos : ∀ n : ℕ, 1 ≤ n → 0 < threeHalvesTerm n) :
    Summable threeHalvesTerm := by
  unfold threeHalvesTerm
  exact Real.summable_one_div_nat_rpow.mpr (by norm_num)

theorem gap5
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < rootTerm n)
    (hcompare : ∀ n : ℕ, 1 ≤ n → rootTerm n < threeHalvesTerm n)
    (hpowerPos : ∀ n : ℕ, 1 ≤ n → 0 < threeHalvesTerm n)
    (hpower : Summable threeHalvesTerm) :
    Summable rootTerm := by
  refine hpower.of_norm_bounded ?_
  intro n
  by_cases hn : n = 0
  · subst n
    norm_num [rootTerm, threeHalvesTerm, Real.zero_rpow]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [Real.norm_eq_abs, abs_of_pos (hpos n hn1)]
    exact (hcompare n hn1).le

end

end ProofGap.Exercise2563
