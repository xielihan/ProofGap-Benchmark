import Mathlib

open scoped Topology

-- IsSeq(x) is encoded by x : ℕ → ℝ (the theorem library).
-- Positive indices exclude x 0; Nat encodes the nonnegative integer condition.
def exercise100Values (x : ℕ → ℝ) : Set ℝ :=
  {y | ∃ n : ℕ, 0 < n ∧ y = x n}

-- Take the supremum in the extended reals, before any order operation.
def exercise100ExtendedValues (x : ℕ → ℝ) : Set EReal :=
  {y | ∃ n : ℕ, 0 < n ∧ y = (x n : EReal)}

-- Exercise 100, gap 1
theorem proof_gap_exercise_100_1
  (x : ℕ → ℝ)
  (h_formula : ∀ n : ℕ, 0 < n → x n = (n : ℝ) + 100 / (n : ℝ))
  : ∀ n : ℕ, 0 < n → x n = (Real.sqrt (n : ℝ) - 10 / Real.sqrt (n : ℝ)) ^ 2 + 20 := by
  sorry

-- Exercise 100, gap 2
theorem proof_gap_exercise_100_2
  (x : ℕ → ℝ)
  (h_formula : ∀ n : ℕ, 0 < n → x n = (n : ℝ) + 100 / (n : ℝ))
  (h_gap_1 : ∀ n : ℕ, 0 < n → x n = (Real.sqrt (n : ℝ) - 10 / Real.sqrt (n : ℝ)) ^ 2 + 20)
  : ∀ n : ℕ, 0 < n → 20 ≤ x n := by
  sorry

-- Exercise 100, gap 3
theorem proof_gap_exercise_100_3
  (x : ℕ → ℝ)
  (h_formula : ∀ n : ℕ, 0 < n → x n = (n : ℝ) + 100 / (n : ℝ))
  (h_gap_1 : ∀ n : ℕ, 0 < n → x n = (Real.sqrt (n : ℝ) - 10 / Real.sqrt (n : ℝ)) ^ 2 + 20)
  (h_gap_2 : ∀ n : ℕ, 0 < n → 20 ≤ x n)
  : x 10 = 20 := by
  sorry

-- Exercise 100, gap 4
theorem proof_gap_exercise_100_4
  (x : ℕ → ℝ)
  (h_formula : ∀ n : ℕ, 0 < n → x n = (n : ℝ) + 100 / (n : ℝ))
  (h_gap_1 : ∀ n : ℕ, 0 < n → x n = (Real.sqrt (n : ℝ) - 10 / Real.sqrt (n : ℝ)) ^ 2 + 20)
  (h_gap_2 : ∀ n : ℕ, 0 < n → 20 ≤ x n)
  (h_gap_3 : x 10 = 20)
  : IsLeast (exercise100Values x) 20 := by
  sorry

-- Exercise 100, gap 5
theorem proof_gap_exercise_100_5
  (x : ℕ → ℝ)
  (h_formula : ∀ n : ℕ, 0 < n → x n = (n : ℝ) + 100 / (n : ℝ))
  (h_gap_1 : ∀ n : ℕ, 0 < n → x n = (Real.sqrt (n : ℝ) - 10 / Real.sqrt (n : ℝ)) ^ 2 + 20)
  (h_gap_2 : ∀ n : ℕ, 0 < n → 20 ≤ x n)
  (h_gap_3 : x 10 = 20)
  (h_gap_4 : IsLeast (exercise100Values x) 20)
  : sInf (exercise100Values x) = 20 := by
  sorry

-- Exercise 100, gap 6
theorem proof_gap_exercise_100_6
  (x : ℕ → ℝ)
  (h_formula : ∀ n : ℕ, 0 < n → x n = (n : ℝ) + 100 / (n : ℝ))
  (h_gap_1 : ∀ n : ℕ, 0 < n → x n = (Real.sqrt (n : ℝ) - 10 / Real.sqrt (n : ℝ)) ^ 2 + 20)
  (h_gap_2 : ∀ n : ℕ, 0 < n → 20 ≤ x n)
  (h_gap_3 : x 10 = 20)
  (h_gap_4 : IsLeast (exercise100Values x) 20)
  (h_gap_5 : sInf (exercise100Values x) = 20)
  : sSup (exercise100ExtendedValues x) = (⊤ : EReal) := by
  sorry

-- Exercise 100, gap 7
theorem proof_gap_exercise_100_7
  (x : ℕ → ℝ)
  (h_formula : ∀ n : ℕ, 0 < n → x n = (n : ℝ) + 100 / (n : ℝ))
  (h_gap_1 : ∀ n : ℕ, 0 < n → x n = (Real.sqrt (n : ℝ) - 10 / Real.sqrt (n : ℝ)) ^ 2 + 20)
  (h_gap_2 : ∀ n : ℕ, 0 < n → 20 ≤ x n)
  (h_gap_3 : x 10 = 20)
  (h_gap_4 : IsLeast (exercise100Values x) 20)
  (h_gap_5 : sInf (exercise100Values x) = 20)
  (h_gap_6 : sSup (exercise100ExtendedValues x) = (⊤ : EReal))
  : Filter.limsup (fun n : ℕ => (x n : EReal)) Filter.atTop = (⊤ : EReal) := by
  sorry

-- Exercise 100, gap 8
theorem proof_gap_exercise_100_8
  (x : ℕ → ℝ)
  (h_formula : ∀ n : ℕ, 0 < n → x n = (n : ℝ) + 100 / (n : ℝ))
  (h_gap_1 : ∀ n : ℕ, 0 < n → x n = (Real.sqrt (n : ℝ) - 10 / Real.sqrt (n : ℝ)) ^ 2 + 20)
  (h_gap_2 : ∀ n : ℕ, 0 < n → 20 ≤ x n)
  (h_gap_3 : x 10 = 20)
  (h_gap_4 : IsLeast (exercise100Values x) 20)
  (h_gap_5 : sInf (exercise100Values x) = 20)
  (h_gap_6 : sSup (exercise100ExtendedValues x) = (⊤ : EReal))
  (h_gap_7 : Filter.limsup (fun n : ℕ => (x n : EReal)) Filter.atTop = (⊤ : EReal))
  : Filter.Tendsto (fun n : ℕ => (x n : EReal)) Filter.atTop (𝓝 (⊤ : EReal)) := by
  sorry

