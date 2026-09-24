import Mathlib

open Filter
open scoped Topology

namespace Exercise125

-- All sequence statements concern positive indices; the value at zero is unrestricted.
def Bounds (x : ℕ → ℝ) (a0 b0 : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → a0 ≤ x n ∧ x n ≤ b0

def SubseqIndex (p : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → 0 < p k ∧ p k < p (k + 1)

def Converges (x : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, Tendsto x atTop (𝓝 c)

def IntervalAt (x a b : ℕ → ℝ) (I0 : Set ℝ) (a0 b0 : ℝ) (k : ℕ) : Prop :=
  Set.Icc (a k) (b k) ⊆ I0 ∧
  Set.Infinite {n : ℕ | 0 < n ∧ x n ∈ Set.Icc (a k) (b k)} ∧
  b k - a k = (b0 - a0) / (2 : ℝ) ^ k

-- The unused outer k and independent inner j preserve the source's shadowing.
-- Scalar a,b in b-a are named a0,b0, as established by the original text.
def IntervalExists (x : ℕ → ℝ) (I0 : Set ℝ) (a0 b0 : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ (a : ℕ → ℝ) (j : ℕ) (b : ℕ → ℝ),
    0 < j ∧ IntervalAt x a b I0 a0 b0 j

def Nested (a b : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → Set.Icc (a (k + 1)) (b (k + 1)) ⊆ Set.Icc (a k) (b k)

def Common (a b : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → c ∈ Set.Icc (a k) (b k)

def Selection (x a b : ℕ → ℝ) (p : ℕ → ℕ) : Prop :=
  SubseqIndex p ∧ ∀ k : ℕ, 0 < k →
    0 < p k ∧ p k < p (k + 1) ∧ x (p k) ∈ Set.Icc (a k) (b k)

def SelectionExists (x a b : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ (p : ℕ → ℕ) (j : ℕ),
    SubseqIndex p ∧ 0 < j ∧ 0 < p j ∧ p j < p (j + 1) ∧ x (p j) ∈ Set.Icc (a j) (b j)

end Exercise125
open Exercise125

-- Exercise 125, gap 1
theorem proof_gap_exercise_125_1
  (x : ℕ → ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  : ∃ a0 b0 : ℝ, Bounds x a0 b0 := by
  sorry

-- Exercise 125, gap 2
theorem proof_gap_exercise_125_2
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : ∃ a0 b0 : ℝ, Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  : IntervalExists x I0 a0 b0 := by
  sorry

-- Exercise 125, gap 3
theorem proof_gap_exercise_125_3
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : ∃ a0 b0 : ℝ, Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : IntervalExists x I0 a0 b0)
  : Nested a b := by
  sorry

-- Exercise 125, gap 4
theorem proof_gap_exercise_125_4
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : ∀ k : ℕ, 0 < k → IntervalAt x a b I0 a0 b0 k)
  (h6 : Nested a b)
  : ∃ d : ℝ, Common a b d := by
  sorry

-- Exercise 125, gap 5
theorem proof_gap_exercise_125_5
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ) (c : ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : ∀ k : ℕ, 0 < k → IntervalAt x a b I0 a0 b0 k)
  (h6 : Nested a b)
  (h7 : Common a b c)
  : Converges a := by
  sorry

-- Exercise 125, gap 6
theorem proof_gap_exercise_125_6
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ) (c : ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : ∀ k : ℕ, 0 < k → IntervalAt x a b I0 a0 b0 k)
  (h6 : Nested a b)
  (h7 : Common a b c)
  (h8 : Tendsto a atTop (𝓝 c))
  : Converges b := by
  sorry

-- Exercise 125, gap 7
theorem proof_gap_exercise_125_7
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : ∃ a0 b0 : ℝ, Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : IntervalExists x I0 a0 b0)
  (h6 : Nested a b)
  (h7 : ∃ d : ℝ, Common a b d)
  (h8 : Converges a)
  (h9 : Converges b)
  : SelectionExists x a b := by
  sorry

-- Exercise 125, gap 8
theorem proof_gap_exercise_125_8
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ) (c : ℝ) (p : ℕ → ℕ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : ∀ k : ℕ, 0 < k → IntervalAt x a b I0 a0 b0 k)
  (h6 : Nested a b)
  (h7 : Common a b c)
  (h8 : Tendsto a atTop (𝓝 c))
  (h9 : Tendsto b atTop (𝓝 c))
  (h10 : Selection x a b p)
  : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → a k ≤ x (q k) := by
  sorry

-- Exercise 125, gap 9
theorem proof_gap_exercise_125_9
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ) (c : ℝ) (p : ℕ → ℕ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : ∀ k : ℕ, 0 < k → IntervalAt x a b I0 a0 b0 k)
  (h6 : Nested a b)
  (h7 : Common a b c)
  (h8 : Tendsto a atTop (𝓝 c))
  (h9 : Tendsto b atTop (𝓝 c))
  (h10 : Selection x a b p)
  (h11 : ∀ k : ℕ, 0 < k → a k ≤ x (p k))
  : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → x (q k) ≤ b k := by
  sorry

-- Exercise 125, gap 10
theorem proof_gap_exercise_125_10
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ) (c : ℝ) (p : ℕ → ℕ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : ∀ k : ℕ, 0 < k → IntervalAt x a b I0 a0 b0 k)
  (h6 : Nested a b)
  (h7 : Common a b c)
  (h8 : Tendsto a atTop (𝓝 c))
  (h9 : Tendsto b atTop (𝓝 c))
  (h10 : Selection x a b p)
  (h11 : ∀ k : ℕ, 0 < k → a k ≤ x (p k))
  (h12 : ∀ k : ℕ, 0 < k → x (p k) ≤ b k)
  : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, ∀ k : ℕ, 0 < k → |x (q k) - d| ≤ b k - a k := by
  sorry

-- Exercise 125, gap 11
theorem proof_gap_exercise_125_11
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : ∃ a0 b0 : ℝ, Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : IntervalExists x I0 a0 b0)
  (h6 : Nested a b)
  (h7 : ∃ d : ℝ, Common a b d)
  (h8 : Converges a)
  (h9 : Converges b)
  (h10 : SelectionExists x a b)
  (h11 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → a k ≤ x (q k))
  (h12 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → x (q k) ≤ b k)
  (h13 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, ∀ k : ℕ, 0 < k → |x (q k) - d| ≤ b k - a k)
  : ∃ q : ℕ → ℕ, SubseqIndex q := by
  sorry

-- Exercise 125, gap 12
theorem proof_gap_exercise_125_12
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ) (c : ℝ) (p : ℕ → ℕ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : ∀ k : ℕ, 0 < k → IntervalAt x a b I0 a0 b0 k)
  (h6 : Nested a b)
  (h7 : Common a b c)
  (h8 : Tendsto a atTop (𝓝 c))
  (h9 : Tendsto b atTop (𝓝 c))
  (h10 : Selection x a b p)
  (h11 : ∀ k : ℕ, 0 < k → a k ≤ x (p k))
  (h12 : ∀ k : ℕ, 0 < k → x (p k) ≤ b k)
  (h13 : ∀ k : ℕ, 0 < k → |x (p k) - c| ≤ b k - a k)
  (h14 : ∃ q : ℕ → ℕ, SubseqIndex q)
  : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, Tendsto (fun k => x (q k)) atTop (𝓝 d) := by
  sorry

-- Exercise 125, gap 13
theorem proof_gap_exercise_125_13
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : ∃ a0 b0 : ℝ, Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : IntervalExists x I0 a0 b0)
  (h6 : Nested a b)
  (h7 : ∃ d : ℝ, Common a b d)
  (h8 : Converges a)
  (h9 : Converges b)
  (h10 : SelectionExists x a b)
  (h11 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → a k ≤ x (q k))
  (h12 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → x (q k) ≤ b k)
  (h13 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, ∀ k : ℕ, 0 < k → |x (q k) - d| ≤ b k - a k)
  (h14 : ∃ q : ℕ → ℕ, SubseqIndex q)
  (h15 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, Tendsto (fun k => x (q k)) atTop (𝓝 d))
  : ∃ q : ℕ → ℕ, SubseqIndex q ∧ Converges (x ∘ q) := by
  sorry

-- Exercise 125, gap 14
theorem proof_gap_exercise_125_14
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : ∃ a0 b0 : ℝ, Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : IntervalExists x I0 a0 b0)
  (h6 : Nested a b)
  (h7 : ∃ d : ℝ, Common a b d)
  (h8 : Converges a)
  (h9 : Converges b)
  (h10 : SelectionExists x a b)
  (h11 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → a k ≤ x (q k))
  (h12 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → x (q k) ≤ b k)
  (h13 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, ∀ k : ℕ, 0 < k → |x (q k) - d| ≤ b k - a k)
  (h14 : ∃ q : ℕ → ℕ, SubseqIndex q)
  (h15 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, Tendsto (fun k => x (q k)) atTop (𝓝 d))
  (h16 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ Converges (x ∘ q))
  : ∃ q : ℕ → ℕ, SubseqIndex q ∧ Converges (x ∘ q) := by
  sorry

-- Exercise 125, gap 15
theorem proof_gap_exercise_125_15
  (x : ℕ → ℝ) (a0 b0 : ℝ) (I0 : Set ℝ) (a b : ℕ → ℝ)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, 0 < n → |x n| ≤ M)
  (h3 : ∃ a0 b0 : ℝ, Bounds x a0 b0)
  (h4 : I0 = Set.Icc a0 b0)
  (h5 : IntervalExists x I0 a0 b0)
  (h6 : Nested a b)
  (h7 : ∃ d : ℝ, Common a b d)
  (h8 : Converges a)
  (h9 : Converges b)
  (h10 : SelectionExists x a b)
  (h11 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → a k ≤ x (q k))
  (h12 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∀ k : ℕ, 0 < k → x (q k) ≤ b k)
  (h13 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, ∀ k : ℕ, 0 < k → |x (q k) - d| ≤ b k - a k)
  (h14 : ∃ q : ℕ → ℕ, SubseqIndex q)
  (h15 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ ∃ d : ℝ, Tendsto (fun k => x (q k)) atTop (𝓝 d))
  (h16 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ Converges (x ∘ q))
  (h17 : ∃ q : ℕ → ℕ, SubseqIndex q ∧ Converges (x ∘ q))
  : ∃ q : ℕ → ℕ, SubseqIndex q ∧ Converges (x ∘ q) := by
  sorry

