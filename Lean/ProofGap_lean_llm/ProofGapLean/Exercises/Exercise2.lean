import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ext

/-!
# Exercise 2

Semantic Lean formalization of:

* Exercise 2, gap 1
* ...
* Exercise 2, gap 9

The source proves the sum-of-squares identity by induction.  Natural-number
indices are summed in `ℚ`, which gives the source operation `frac` its standard
field meaning and avoids silently interpreting `1 / 6` as natural division.
-/

namespace ProofGap.Exercise2

/-- `∑ i = 1, ..., n, i²`, interpreted as a rational-valued finite sum. -/
def sumSquares (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ 2

/-- `n(n+1)(2n+1)/6`, with `n` embedded in the rationals. -/
def closedForm (n : ℕ) : ℚ :=
  (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) / 6

/-- The mathematical assertion used as the induction predicate. -/
def SumSquaresFormula (n : ℕ) : Prop :=
  sumSquares n = closedForm n

/-- The factored expression occurring in the source induction step. -/
def expandedSuccessorForm (k : ℕ) : ℚ :=
  (1 / 6 : ℚ) * ((k : ℚ) + 1) *
    ((k : ℚ) * (2 * (k : ℚ) + 1) + 6 * ((k : ℚ) + 1))

private theorem sumSquares_succ (k : ℕ) :
    sumSquares (k + 1) = sumSquares k + ((k : ℚ) + 1) ^ 2 := by
  have hnot : k + 1 ∉ Finset.Icc 1 k := by
    simp
  have hset :
      Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [sumSquares, sumSquares, hset, Finset.sum_insert hnot]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Exercise 2, gap 1. -/
theorem gap1 :
    ∀ n : ℕ, n = 1 → SumSquaresFormula n := by
  intro n hn
  subst n
  norm_num [SumSquaresFormula, sumSquares, closedForm]

/--
Exercise 2, gap 2.

The source introduces the induction case with `n = k` but omits the induction
hypothesis.  `SumSquaresFormula n` is added as the missing premise.
-/
theorem gap2
    (h1 : ∀ n : ℕ, n = 1 → SumSquaresFormula n) :
    ∀ n k : ℕ, n = k → SumSquaresFormula n → SumSquaresFormula k := by
  intro n k hnk hn
  subst k
  exact hn

/-- Exercise 2, gap 3; the missing induction hypothesis is explicit. -/
theorem gap3
    (h1 : ∀ n : ℕ, n = 1 → SumSquaresFormula n)
    (h2 : ∀ n k : ℕ, n = k → SumSquaresFormula n → SumSquaresFormula k) :
    ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares k + ((k : ℚ) + 1) ^ 2 =
        closedForm k + ((k : ℚ) + 1) ^ 2 := by
  intro n k hnk hn
  subst k
  change sumSquares n = closedForm n at hn
  exact congrArg (fun q : ℚ => q + ((n : ℚ) + 1) ^ 2) hn

/-- Exercise 2, gap 4; the missing induction hypothesis is explicit. -/
theorem gap4
    (h1 : ∀ n : ℕ, n = 1 → SumSquaresFormula n)
    (h2 : ∀ n k : ℕ, n = k → SumSquaresFormula n → SumSquaresFormula k)
    (h3 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares k + ((k : ℚ) + 1) ^ 2 =
        closedForm k + ((k : ℚ) + 1) ^ 2) :
    ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares (k + 1) = expandedSuccessorForm k := by
  intro n k hnk hn
  rw [sumSquares_succ]
  change sumSquares n = closedForm n at hn
  rw [← hnk, hn]
  simp only [closedForm, expandedSuccessorForm]
  ring

/-- Exercise 2, gap 5. -/
theorem gap5
    (h1 : ∀ n : ℕ, n = 1 → SumSquaresFormula n)
    (h2 : ∀ n k : ℕ, n = k → SumSquaresFormula n → SumSquaresFormula k)
    (h3 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares k + ((k : ℚ) + 1) ^ 2 =
        closedForm k + ((k : ℚ) + 1) ^ 2)
    (h4 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares (k + 1) = expandedSuccessorForm k) :
    ∀ n k : ℕ, n = k →
      expandedSuccessorForm k = closedForm (k + 1) := by
  intro n k hnk
  simp only [expandedSuccessorForm, closedForm]
  push_cast
  ring

/-- Exercise 2, gap 6; the missing induction hypothesis is explicit. -/
theorem gap6
    (h1 : ∀ n : ℕ, n = 1 → SumSquaresFormula n)
    (h2 : ∀ n k : ℕ, n = k → SumSquaresFormula n → SumSquaresFormula k)
    (h3 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares k + ((k : ℚ) + 1) ^ 2 =
        closedForm k + ((k : ℚ) + 1) ^ 2)
    (h4 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares (k + 1) = expandedSuccessorForm k)
    (h5 : ∀ n k : ℕ, n = k →
      expandedSuccessorForm k = closedForm (k + 1)) :
    ∀ n k : ℕ, n = k → SumSquaresFormula n →
      SumSquaresFormula (k + 1) := by
  intro n k hnk hn
  change sumSquares (k + 1) = closedForm (k + 1)
  calc
    sumSquares (k + 1) = expandedSuccessorForm k := h4 n k hnk hn
    _ = closedForm (k + 1) := h5 n k hnk

/--
Exercise 2, gap 7.

This duplicates gap 6 in the source; it is retained because the dataset treats
it as a separate benchmark item.
-/
theorem gap7
    (h1 : ∀ n : ℕ, n = 1 → SumSquaresFormula n)
    (h2 : ∀ n k : ℕ, n = k → SumSquaresFormula n → SumSquaresFormula k)
    (h3 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares k + ((k : ℚ) + 1) ^ 2 =
        closedForm k + ((k : ℚ) + 1) ^ 2)
    (h4 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares (k + 1) = expandedSuccessorForm k)
    (h5 : ∀ n k : ℕ, n = k →
      expandedSuccessorForm k = closedForm (k + 1))
    (h6 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      SumSquaresFormula (k + 1)) :
    ∀ n k : ℕ, n = k → SumSquaresFormula n →
      SumSquaresFormula (k + 1) := by
  exact h6

/--
Exercise 2, gap 8.

The source's positive-integer induction is made explicit: `0 < n` is the
membership condition and the induction step takes the missing hypothesis.
-/
theorem gap8
    (h1 : ∀ n : ℕ, n = 1 → SumSquaresFormula n)
    (h2 : ∀ n k : ℕ, n = k → SumSquaresFormula n → SumSquaresFormula k)
    (h3 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares k + ((k : ℚ) + 1) ^ 2 =
        closedForm k + ((k : ℚ) + 1) ^ 2)
    (h4 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares (k + 1) = expandedSuccessorForm k)
    (h5 : ∀ n k : ℕ, n = k →
      expandedSuccessorForm k = closedForm (k + 1))
    (h6 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      SumSquaresFormula (k + 1))
    (h7 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      SumSquaresFormula (k + 1)) :
    ∀ n : ℕ, 0 < n → SumSquaresFormula n := by
  intro n hn
  exact Nat.le_induction
    (h1 1 rfl)
    (fun k _ ih => h7 k k rfl ih)
    n hn

/--
Exercise 2, gap 9.

The source drops the positive-integer qualifier.  Over `ℕ`, the additional
zero case is meaningful and the same identity holds at zero.
-/
theorem gap9
    (h1 : ∀ n : ℕ, n = 1 → SumSquaresFormula n)
    (h2 : ∀ n k : ℕ, n = k → SumSquaresFormula n → SumSquaresFormula k)
    (h3 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares k + ((k : ℚ) + 1) ^ 2 =
        closedForm k + ((k : ℚ) + 1) ^ 2)
    (h4 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      sumSquares (k + 1) = expandedSuccessorForm k)
    (h5 : ∀ n k : ℕ, n = k →
      expandedSuccessorForm k = closedForm (k + 1))
    (h6 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      SumSquaresFormula (k + 1))
    (h7 : ∀ n k : ℕ, n = k → SumSquaresFormula n →
      SumSquaresFormula (k + 1))
    (h8 : ∀ n : ℕ, 0 < n → SumSquaresFormula n) :
    ∀ n : ℕ, SumSquaresFormula n := by
  intro n
  cases n with
  | zero =>
      norm_num [SumSquaresFormula, sumSquares, closedForm]
  | succ k =>
      exact h8 (k + 1) (by omega)

end ProofGap.Exercise2
