import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ConvergentSeries (a : ℕ -> ℝ) : Prop := Summable a
def UniformConvergent (F : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop := TendstoUniformlyOn F g atTop s
noncomputable def rootChoice2769 (n : ℕ) : ℝ := 1 /. (Real.rpow 2 (1 /. (n + 1)))

-- exercise: exercise_2769

-- GAP 1
theorem proof_gap_exercise_2769_1 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) (k : ℕ)
    (h5 : ∀ n x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ (Set.univ : Set ℕ) ∧ x ∈ Set.Icc (0 : ℝ) 1 →
      S_n n x = (∑ j ∈ Finset.Icc 0 n, (1 - x) * x ^ j))
    (h6 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (0 : ℝ) 1 →
      f x = (1 - x) * x ^ n) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ (Set.univ : Set ℕ) ∧ 0 ≤ x ∧ x ≤ 1 →
        S_n n x = (∑ j ∈ Finset.Icc 0 n, (1 - x) * x ^ j) := by
  sorry

-- GAP 2
theorem proof_gap_exercise_2769_2 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ (Set.univ : Set ℕ) ∧ 0 ≤ x ∧ x ≤ 1 →
        (∑ j ∈ Finset.Icc 0 n, (1 - x) * x ^ j) = (1 - x) * (∑ j ∈ Finset.Icc 0 n, x ^ j) := by
  sorry

-- GAP 3
theorem proof_gap_exercise_2769_3 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ (Set.univ : Set ℕ) ∧ 0 ≤ x ∧ x ≤ 1 →
        (1 - x) * (∑ j ∈ Finset.Icc 0 n, x ^ j) = 1 - x ^ (n + 1) := by
  sorry

-- GAP 4
theorem proof_gap_exercise_2769_4 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ (Set.univ : Set ℕ) ∧ 0 ≤ x ∧ x ≤ 1 →
        S_n n x = 1 - x ^ (n + 1) := by
  sorry

-- GAP 5
theorem proof_gap_exercise_2769_5 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 → S x = 1 := by
  sorry

-- GAP 6
theorem proof_gap_exercise_2769_6 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) : S 1 = 0 := by
  sorry

-- GAP 7
theorem proof_gap_exercise_2769_7 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (0 : ℝ) 1 →
      Tendsto (fun n : ℕ => S_n n x) atTop (𝓝 (S x)) := by
  sorry

-- GAP 8
theorem proof_gap_exercise_2769_8 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∃ xseq : ℕ -> ℝ, ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ xseq n = rootChoice2769 n → 0 < xseq n := by
  sorry

-- GAP 9
theorem proof_gap_exercise_2769_9 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∃ xseq : ℕ -> ℝ, ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ xseq n = rootChoice2769 n → xseq n < 1 := by
  sorry

-- GAP 10
theorem proof_gap_exercise_2769_10 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∃ xseq : ℕ -> ℝ, ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ xseq n = rootChoice2769 n →
      |S_n n (xseq n) - S (xseq n)| = |(1 /. 2) - 1| := by
  sorry

-- GAP 11
theorem proof_gap_exercise_2769_11 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∃ xseq : ℕ -> ℝ, ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ xseq n = rootChoice2769 n →
      |(1 /. 2) - 1| = 1 /. 2 := by
  sorry

-- GAP 12
theorem proof_gap_exercise_2769_12 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) (epsilon0 : ℝ)
    (h14 : epsilon0 = 1 /. 4) :
    ∃ xseq : ℕ -> ℝ, ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ xseq n = rootChoice2769 n →
      (1 /. 2) > epsilon0 := by
  sorry

-- GAP 13
theorem proof_gap_exercise_2769_13 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) (epsilon0 : ℝ)
    (h14 : epsilon0 = 1 /. 4) :
    ∃ xseq : ℕ -> ℝ, ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ xseq n = rootChoice2769 n →
      |S_n n (xseq n) - S (xseq n)| > epsilon0 := by
  sorry

-- GAP 14
theorem proof_gap_exercise_2769_14 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (0 : ℝ) 1 →
      ConvergentSeries (fun n : ℕ => (1 - x) * x ^ n) := by
  sorry

-- GAP 15
theorem proof_gap_exercise_2769_15 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    ¬ UniformConvergent S_n (Set.Icc (0 : ℝ) 1) S := by
  sorry

-- GAP 16
theorem proof_gap_exercise_2769_16 (S_n : ℕ -> ℝ -> ℝ) (S f : ℝ -> ℝ) :
    (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (0 : ℝ) 1 →
      ConvergentSeries (fun n : ℕ => (1 - x) * x ^ n)) ∧
      ¬ UniformConvergent S_n (Set.Icc (0 : ℝ) 1) S := by
  sorry
