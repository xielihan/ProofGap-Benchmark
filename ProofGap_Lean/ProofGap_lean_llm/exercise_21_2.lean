import Mathlib

open scoped BigOperators

namespace Exercise21_2

-- IsSeq is encoded by a : ℕ → ℝ; see the theorem library.
-- Integer indices below are positive, so Int.toNat preserves their value.
def Conditions (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : Prop :=
  (0 < n ∧ x ∈ (Set.univ : Set ℝ)) ∧
    ∀ i : ℤ, (i ∈ (Set.univ : Set ℤ) ∧ 1 ≤ i ∧ i ≤ (n : ℤ)) →
      a i.toNat ∈ (Set.univ : Set ℝ)

def ReverseTriangle (a : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ, Conditions a n x →
    |x + ∑ i ∈ Finset.Icc 1 n, a i| ≥ |x| - |∑ i ∈ Finset.Icc 1 n, a i|

def SumTriangle (a : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ, Conditions a n x →
    |∑ i ∈ Finset.Icc 1 n, a i| ≤ ∑ i ∈ Finset.Icc 1 n, |a i|

def Conclusion (a : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ, Conditions a n x →
    |x + ∑ i ∈ Finset.Icc 1 n, a i| ≥ |x| - (∑ i ∈ Finset.Icc 1 n, |a i|)

end Exercise21_2

open Exercise21_2

-- Exercise 21_2, gap 1 (PROOF GAP @1)
theorem proof_gap_exercise_21_2_1
  (x_i : ℕ → ℝ)
  : ReverseTriangle x_i := by
  sorry

-- Exercise 21_2, gap 2 (PROOF GAP @2)
theorem proof_gap_exercise_21_2_2
  (x_i : ℕ → ℝ)
  (h2 : ReverseTriangle x_i)
  : SumTriangle x_i := by
  sorry

-- Exercise 21_2, gap 3 (PROOF GAP @3)
theorem proof_gap_exercise_21_2_3
  (x_i : ℕ → ℝ)
  (h2 : ReverseTriangle x_i)
  (h3 : SumTriangle x_i)
  : Conclusion x_i := by
  sorry

-- Exercise 21_2, gap 4 (PROOF GAP @4)
theorem proof_gap_exercise_21_2_4
  (x_i : ℕ → ℝ)
  (h2 : ReverseTriangle x_i)
  (h3 : SumTriangle x_i)
  (h4 : Conclusion x_i)
  : Conclusion x_i := by
  sorry

-- Exercise 21_2, gap 5 (PROOF GAP @5)
theorem proof_gap_exercise_21_2_5
  (x_i : ℕ → ℝ)
  (h2 : ReverseTriangle x_i)
  (h3 : SumTriangle x_i)
  (h4 : Conclusion x_i)
  (h5 : Conclusion x_i)
  : Conclusion x_i := by
  sorry

