import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ConvergentSeries (a : ℕ -> ℝ) : Prop := Summable a
def UniformConvergent (F : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop := TendstoUniformlyOn F g atTop s
def PosRealSet : Set ℝ := {x | 0 < x}

-- exercise: exercise_2771

-- GAP 1
theorem proof_gap_exercise_2771_1 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
        S_n n x = ∑ j ∈ Finset.Icc 1 n, x /. ((((j - 1 : ℕ) : ℝ) * x + 1) * ((j : ℝ) * x + 1)) := by
  sorry

-- GAP 2
theorem proof_gap_exercise_2771_2 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
        (∑ j ∈ Finset.Icc 1 n, x /. ((((j - 1 : ℕ) : ℝ) * x + 1) * ((j : ℝ) * x + 1))) =
          ∑ j ∈ Finset.Icc 1 n, (1 /. (((j - 1 : ℕ) : ℝ) * x + 1) - 1 /. ((j : ℝ) * x + 1)) := by
  sorry

-- GAP 3
theorem proof_gap_exercise_2771_3 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
        (∑ j ∈ Finset.Icc 1 n, (1 /. (((j - 1 : ℕ) : ℝ) * x + 1) - 1 /. ((j : ℝ) * x + 1))) =
          1 - 1 /. ((n : ℝ) * x + 1) := by
  sorry

-- GAP 4
theorem proof_gap_exercise_2771_4 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → ∀ x : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
        S_n n x = 1 - 1 /. ((n : ℝ) * x + 1) := by
  sorry

-- GAP 5
theorem proof_gap_exercise_2771_5 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet →
      S x = 1 ∧ Tendsto (fun n : ℕ => S_n n x) atTop (𝓝 1) := by
  sorry

-- GAP 6
theorem proof_gap_exercise_2771_6 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∃ xseq : (ℕ → ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} ∧ xseq n = 1 / (n : ℝ) →
      xseq n ∈ PosRealSet := by
  sorry

-- GAP 7
theorem proof_gap_exercise_2771_7 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∃ xseq : (ℕ → ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} ∧ xseq n = 1 / (n : ℝ) →
      |S_n n (xseq n) - S (xseq n)| = (1 /. 2) := by
  sorry

-- GAP 8
theorem proof_gap_exercise_2771_8 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (epsilon0 : ℝ)
    (h10 : epsilon0 = (1 /. 4)) :
    ∃ xseq : (ℕ → ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} ∧ xseq n = 1 / (n : ℝ) →
      (1 /. 2) > epsilon0 := by
  sorry

-- GAP 9
theorem proof_gap_exercise_2771_9 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (epsilon0 : ℝ)
    (h10 : epsilon0 = (1 /. 4)) :
    ∃ xseq : (ℕ → ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} ∧ xseq n = 1 / (n : ℝ) →
      |S_n n (xseq n) - S (xseq n)| > epsilon0 := by
  sorry

-- GAP 10
theorem proof_gap_exercise_2771_10 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet →
      ConvergentSeries (fun n : ℕ => if 1 ≤ n then x /. ((((n - 1 : ℕ) : ℝ) * x + 1) * ((n : ℝ) * x + 1)) else 0) := by
  sorry

-- GAP 11
theorem proof_gap_exercise_2771_11 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    ¬ UniformConvergent S_n PosRealSet S := by
  sorry

-- GAP 12
theorem proof_gap_exercise_2771_12 (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) :
    (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet →
      ConvergentSeries (fun n : ℕ => if 1 ≤ n then x /. ((((n - 1 : ℕ) : ℝ) * x + 1) * ((n : ℝ) * x + 1)) else 0)) ∧
      ¬ UniformConvergent S_n PosRealSet S := by
  sorry
