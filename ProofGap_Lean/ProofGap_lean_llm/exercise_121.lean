import Mathlib

open Filter
open scoped Topology

namespace Exercise121

-- Integer arithmetic is performed BEFORE conversion to a sequence index.
-- For n ≥ 2, p > 0 and 1 ≤ i ≤ p the argument of toNat is positive.
-- In limits, indices with n < 2 are irrelevant to atTop.
def blockTerm (x : ℕ → ℝ) (p : ℕ) (i n : ℤ) : ℝ :=
  x (((n - 2) * (p : ℤ) + i).toNat)

def blockLimit (x : ℕ → ℝ) (p : ℕ) (i : ℤ) (L : ℝ) : Prop :=
  Tendsto (fun k : ℤ => blockTerm x p i k) atTop (𝓝 L)

def prescribedValues (a : ℤ → ℝ) (p : ℕ) : Set ℝ :=
  {y | ∃ i : ℤ, 1 ≤ i ∧ i ≤ (p : ℤ) ∧ y = a i}

-- the theorem library, Thm 229: arbitrarily late terms
-- lie within every positive epsilon of a sequence accumulation point.
def accumulationPoints (x : ℕ → ℝ) : Set ℝ :=
  {L | ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ |x n - L| < ε}

end Exercise121

open Exercise121

-- IsSeq(x) is encoded by x : ℕ → ℝ (Thm 294 in the predicate definitions).
-- Membership in IntegerSet/RealSet is encoded by the corresponding types.
-- Exercise 121, gap 1
-- SOURCE ISSUE: a single term equality does not imply the asserted limit.
-- Preserve the source implication and the separate limit binder k.
theorem proof_gap_exercise_121_1
    (a : ℤ → ℝ) (p : ℕ) (x : ℕ → ℝ)
    (hp : 0 < p)
    (ha : ∀ i : ℤ, 1 ≤ i → i ≤ (p : ℤ) → a i ∈ (Set.univ : Set ℝ)) :
    ∀ n : ℤ, ∀ i : ℤ,
      (n ≥ 2 ∧ 1 ≤ i ∧ i ≤ (p : ℤ) ∧
        blockTerm x p i n = a i - 1 / (n : ℝ)) →
      blockLimit x p i (a i) := by
  sorry

-- Exercise 121, gap 2
theorem proof_gap_exercise_121_2
    (a : ℤ → ℝ) (p : ℕ) (x : ℕ → ℝ)
    (hp : 0 < p)
    (ha : ∀ i : ℤ, 1 ≤ i → i ≤ (p : ℤ) → a i ∈ (Set.univ : Set ℝ))
    (hlim : ∀ i : ℤ, 1 ≤ i → i ≤ (p : ℤ) → blockLimit x p i (a i)) :
    prescribedValues a p ⊆ accumulationPoints x := by
  sorry

-- Exercise 121, gap 3
-- The IsSeq conjunct of the conclusion is already guaranteed by x's type.
theorem proof_gap_exercise_121_3
    (a : ℤ → ℝ) (p : ℕ) (x : ℕ → ℝ)
    (hp : 0 < p)
    (ha : ∀ i : ℤ, 1 ≤ i → i ≤ (p : ℤ) → a i ∈ (Set.univ : Set ℝ))
    (hpoint : ∀ n : ℤ, ∀ i : ℤ,
      (n ≥ 2 ∧ 1 ≤ i ∧ i ≤ (p : ℤ) ∧
        blockTerm x p i n = a i - 1 / (n : ℝ)) →
      blockLimit x p i (a i))
    (hacc : prescribedValues a p ⊆ accumulationPoints x) :
    (∀ n i : ℤ, (n ≥ 2 ∧ 1 ≤ i ∧ i ≤ (p : ℤ)) →
      blockTerm x p i n = a i - 1 / (n : ℝ)) →
    prescribedValues a p ⊆ accumulationPoints x := by
  sorry
