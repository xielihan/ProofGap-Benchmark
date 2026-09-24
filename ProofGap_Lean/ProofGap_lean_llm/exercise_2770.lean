import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def UniformConvergent (F : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop := TendstoUniformlyOn F g atTop s

-- exercise: exercise_2770

-- GAP 1
theorem proof_gap_exercise_2770_1 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ -1 ≤ x ∧ x ≤ 1 →
        S_n n x = (∑ j ∈ Finset.Icc 1 n, ((x ^ j) /. j - (x ^ (j + 1)) /. (j + 1))) := by
  sorry

-- GAP 2
theorem proof_gap_exercise_2770_2 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ -1 ≤ x ∧ x ≤ 1 →
        (∑ j ∈ Finset.Icc 1 n, ((x ^ j) /. j - (x ^ (j + 1)) /. (j + 1))) =
          x - ((x ^ (n + 1)) /. (n + 1)) := by
  sorry

-- GAP 3
theorem proof_gap_exercise_2770_3 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ -1 ≤ x ∧ x ≤ 1 →
        S_n n x = x - ((x ^ (n + 1)) /. (n + 1)) := by
  sorry

-- GAP 4
theorem proof_gap_exercise_2770_4 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 →
      S x = x ∧ Tendsto (fun n : ℕ => S_n n x) atTop (𝓝 x) := by
  sorry

-- GAP 5
theorem proof_gap_exercise_2770_5 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Icc (-1 : ℝ) 1 →
      |S_n n x - S x| = ((|x| ^ (n + 1)) /. (n + 1)) ∧
        ((|x| ^ (n + 1)) /. (n + 1)) ≤ (1 /. ((n : ℕ) + 1)) ∧
        (1 /. ((n : ℕ) + 1)) < (1 /. n) := by
  sorry

-- GAP 6
theorem proof_gap_exercise_2770_6 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ N = Int.toNat ⌊1 /. ε⌋ ∧
        ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N ∧ n ∈ ({m : ℕ | 0 < m}) →
          ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 →
            |S_n n x - S x| < (1 /. n) ∧ (1 /. n) < ε := by
  sorry

-- GAP 7
theorem proof_gap_exercise_2770_7 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    UniformConvergent S_n (Set.Icc (-1 : ℝ) 1) S := by
  sorry

-- GAP 8
theorem proof_gap_exercise_2770_8 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ)
    (h11 : UniformConvergent S_n (Set.Icc (-1 : ℝ) 1) S) :
    UniformConvergent S_n (Set.Icc (-1 : ℝ) 1) S := by
  sorry
