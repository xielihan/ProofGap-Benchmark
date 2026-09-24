import Mathlib

-- The unary source f is g; the indexed source f_n (printed f(n,x)) is F.
-- Natural indices include zero; no positivity is silently imposed.
noncomputable def exercise210Closed (n : ℕ) (x : ℝ) : ℝ :=
  x / Real.sqrt (1 + (n : ℝ) * x ^ 2)

noncomputable def exercise210Nested (k : ℕ) (x : ℝ) : ℝ :=
  (x / Real.sqrt (1 + (k : ℝ) * x ^ 2)) /
    Real.sqrt (1 + x ^ 2 / (1 + (k : ℝ) * x ^ 2))

-- Exercise 210, gap 1
theorem proof_gap_exercise_210_1
  (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
  (h2 : ∀ x : ℝ, g x = x / Real.sqrt (1 + x ^ 2))
  (h3 : ∀ (n : ℕ) (x : ℝ), 0 < n → (n = 1 → F n x = g x) ∧ (1 < n → F n x = g (F (n - 1) x)))
  : ∀ (n : ℕ) (x : ℝ), n = 1 → F n x = x / Real.sqrt (1 + x ^ 2) := by
  sorry

-- Exercise 210, gap 2
theorem proof_gap_exercise_210_2
  (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
  (h2 : ∀ x : ℝ, g x = x / Real.sqrt (1 + x ^ 2))
  (h3 : ∀ (n : ℕ) (x : ℝ), 0 < n → F n x = g (F (n - 1) x))
  (h4 : ∀ (n : ℕ) (x : ℝ), n = 1 → F n x = x / Real.sqrt (1 + x ^ 2))
  : ∀ (n : ℕ) (x : ℝ), n = 2 → F n x = x / Real.sqrt (1 + 2 * x ^ 2) := by
  sorry

-- Exercise 210, gap 3
theorem proof_gap_exercise_210_3
  (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
  (h2 : ∀ x : ℝ, g x = x / Real.sqrt (1 + x ^ 2))
  (h3 : ∀ (n : ℕ) (x : ℝ), 0 < n → (n = 1 → F n x = g x) ∧ (1 < n → F n x = g (F (n - 1) x)))
  (h4 : ∀ (n : ℕ) (x : ℝ), n = 1 → F n x = x / Real.sqrt (1 + x ^ 2))
  (h5 : ∀ (n : ℕ) (x : ℝ), n = 2 → F n x = x / Real.sqrt (1 + 2 * x ^ 2))
  : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → F n x = exercise210Nested k x := by
  sorry

-- Exercise 210, gap 4
theorem proof_gap_exercise_210_4
  (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
  (h2 : ∀ x : ℝ, g x = x / Real.sqrt (1 + x ^ 2))
  (h3 : ∀ (n : ℕ) (x : ℝ), 0 < n → (n = 1 → F n x = g x) ∧ (1 < n → F n x = g (F (n - 1) x)))
  (h4 : ∀ (n : ℕ) (x : ℝ), n = 1 → F n x = x / Real.sqrt (1 + x ^ 2))
  (h5 : ∀ (n : ℕ) (x : ℝ), n = 2 → F n x = x / Real.sqrt (1 + 2 * x ^ 2))
  (h6 : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → F n x = exercise210Nested k x)
  : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → exercise210Nested k x = exercise210Closed (k + 1) x := by
  sorry

-- Exercise 210, gap 5
theorem proof_gap_exercise_210_5
  (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
  (h2 : ∀ x : ℝ, g x = x / Real.sqrt (1 + x ^ 2))
  (h3 : ∀ (n : ℕ) (x : ℝ), 0 < n → F n x = g (F (n - 1) x))
  (h4 : ∀ (n : ℕ) (x : ℝ), n = 1 → F n x = x / Real.sqrt (1 + x ^ 2))
  (h5 : ∀ (n : ℕ) (x : ℝ), n = 2 → F n x = x / Real.sqrt (1 + 2 * x ^ 2))
  (h6 : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → F n x = exercise210Nested k x)
  (h7 : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → exercise210Nested k x = exercise210Closed (k + 1) x)
  : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → F n x = exercise210Closed (k + 1) x := by
  sorry

-- Exercise 210, gap 6
-- SOURCE STATEMENT ISSUE: the conclusion asserts positivity even at n = 0.
theorem proof_gap_exercise_210_6
  (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
  (h2 : ∀ x : ℝ, g x = x / Real.sqrt (1 + x ^ 2))
  (h3 : ∀ (n : ℕ) (x : ℝ), 0 < n → F n x = g (F (n - 1) x))
  (h4 : ∀ (n : ℕ) (x : ℝ), n = 1 → F n x = x / Real.sqrt (1 + x ^ 2))
  (h5 : ∀ (n : ℕ) (x : ℝ), n = 2 → F n x = x / Real.sqrt (1 + 2 * x ^ 2))
  (h6 : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → F n x = exercise210Nested k x)
  (h7 : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → exercise210Nested k x = exercise210Closed (k + 1) x)
  (h8 : ∀ (k n : ℕ) (x : ℝ), 0 < k → (∀ y : ℝ, F k y = exercise210Closed k y) → n = k + 1 → F n x = exercise210Closed (k + 1) x)
  : ∀ (n : ℕ) (x : ℝ), (∀ (m : ℕ) (y : ℝ), 0 < m → F m y = exercise210Closed m y) → x ∈ (Set.univ : Set ℝ) ∧ 0 < n := by
  sorry

