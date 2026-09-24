import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2589

noncomputable section

def targetTerm (n : ℕ) : ℝ :=
  Real.rpow n ((n : ℝ) - 1) /
    Real.rpow (2 * (n : ℝ) ^ 2 + n + 1) (((n : ℝ) + 1) / 2)

def comparisonTerm (n : ℕ) : ℝ :=
  Real.rpow n ((n : ℝ) - 1) /
    Real.rpow ((n : ℝ) ^ 2) (((n : ℝ) + 1) / 2)

def inverseSquare (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

private theorem rpowRatioIdentity (x : ℝ) (hx : 0 < x) :
    Real.rpow x (x - 1) /
      Real.rpow (x ^ 2) ((x + 1) / 2) = 1 / x ^ 2 := by
  have hden : Real.rpow (x ^ 2) ((x + 1) / 2) =
      Real.rpow x (x + 1) := by
    calc
      Real.rpow (x ^ 2) ((x + 1) / 2) =
          Real.rpow (Real.rpow x (2 : ℝ)) ((x + 1) / 2) := by
            congr 1
            exact (Real.rpow_natCast x 2).symm
      _ = Real.rpow x ((2 : ℝ) * ((x + 1) / 2)) :=
        (Real.rpow_mul hx.le 2 ((x + 1) / 2)).symm
      _ = Real.rpow x (x + 1) := by
        congr 1
        ring
  rw [hden]
  calc
    Real.rpow x (x - 1) / Real.rpow x (x + 1) =
        Real.rpow x ((x - 1) - (x + 1)) :=
      (Real.rpow_sub hx (x - 1) (x + 1)).symm
    _ = Real.rpow x (-(2 : ℝ)) := by congr 1 <;> ring
    _ = Inv.inv (Real.rpow x (2 : ℝ)) := Real.rpow_neg hx.le 2
    _ = Inv.inv (x ^ (2 : ℕ)) := congrArg Inv.inv (Real.rpow_natCast x 2)
    _ = 1 / x ^ (2 : ℕ) := by rw [one_div]

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → 0 < targetTerm n := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold targetTerm
  apply div_pos
  · exact Real.rpow_pos_of_pos hnpos _
  · apply Real.rpow_pos_of_pos
    positivity

theorem gap2
    (hpositive : ∀ n : ℕ, 1 ≤ n → 0 < targetTerm n) :
    ∀ n : ℕ, 1 ≤ n → targetTerm n < comparisonTerm n := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnum : 0 < Real.rpow (n : ℝ) ((n : ℝ) - 1) :=
    Real.rpow_pos_of_pos hnpos _
  have hexponent : 0 < (((n : ℝ) + 1) / 2) := by positivity
  have hbase : (n : ℝ) ^ 2 < 2 * (n : ℝ) ^ 2 + n + 1 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hden := Real.rpow_lt_rpow (sq_nonneg (n : ℝ)) hbase hexponent
  unfold targetTerm comparisonTerm
  exact div_lt_div_of_pos_left hnum
    (Real.rpow_pos_of_pos (sq_pos_of_pos hnpos) _) hden

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n → comparisonTerm n = inverseSquare n := by
  intro n hn
  unfold comparisonTerm inverseSquare
  apply rpowRatioIdentity
  exact_mod_cast hn

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n → 0 < inverseSquare n := by
  intro n hn
  unfold inverseSquare
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem gap5 :
    Summable inverseSquare := by
  unfold inverseSquare
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

theorem gap6
    (hpositive : ∀ n : ℕ, 1 ≤ n → 0 < targetTerm n)
    (hcompare : ∀ n : ℕ, 1 ≤ n → targetTerm n < comparisonTerm n)
    (hidentity : ∀ n : ℕ, 1 ≤ n →
      comparisonTerm n = inverseSquare n)
    (hsum : Summable inverseSquare) :
    Summable targetTerm := by
  apply Summable.of_nonneg_of_le (f := inverseSquare)
  · intro n
    by_cases hn : 1 ≤ n
    · exact (hpositive n hn).le
    · have : n = 0 := by omega
      subst n
      norm_num [targetTerm]
  · intro n
    by_cases hn : 1 ≤ n
    · exact (hcompare n hn).le.trans_eq (hidentity n hn)
    · have : n = 0 := by omega
      subst n
      norm_num [targetTerm, inverseSquare]
  · exact hsum

theorem gap7
    (hsum : Summable targetTerm) :
    Summable targetTerm := hsum

end

end ProofGap.Exercise2589
