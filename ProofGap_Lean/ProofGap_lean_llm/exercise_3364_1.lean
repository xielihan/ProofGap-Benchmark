import Mathlib

set_option linter.style.longLine false

-- exercise: exercise_3364_1

def lpHasDomain (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  s.Nonempty ∨ s = ∅

def lpCircleSolutionOn (y : ℝ -> ℝ) : Prop :=
  lpHasDomain y (Set.Icc (-1 : ℝ) 1) ∧
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1

noncomputable def lpYn (n : ℕ) : ℝ -> ℝ :=
  fun x => if x = (1 : ℝ) / n then -Real.sqrt (1 - x ^ (2 : ℕ)) else Real.sqrt (1 - x ^ (2 : ℕ))

-- PROOF GAP @1
theorem proof_gap_exercise_3364_1_1
  (y : ℝ -> ℝ) (y_n : ℕ -> ℝ -> ℝ) (n : ℕ)
  (hn : 0 < n)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : ∀ n : ℕ, 0 < n → y_n n = lpYn n)
  : ∀ n : ℕ, 0 < n → lpHasDomain (y_n n) (Set.Icc (-1 : ℝ) 1) := by
  sorry

-- PROOF GAP @2
theorem proof_gap_exercise_3364_1_2
  (y : ℝ -> ℝ) (y_n : ℕ -> ℝ -> ℝ) (n : ℕ)
  (hn : 0 < n)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : ∀ n : ℕ, 0 < n → y_n n = lpYn n)
  (h4 : ∀ n : ℕ, 0 < n → lpHasDomain (y_n n) (Set.Icc (-1 : ℝ) 1))
  : ∀ n : ℕ, 0 < n → ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      x ^ (2 : ℕ) + (y_n n x) ^ (2 : ℕ) = 1 := by
  sorry

-- PROOF GAP @3
theorem proof_gap_exercise_3364_1_3
  (y : ℝ -> ℝ) (y_n : ℕ -> ℝ -> ℝ) (n : ℕ)
  (hn : 0 < n)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : ∀ n : ℕ, 0 < n → y_n n = lpYn n)
  (h4 : ∀ n : ℕ, 0 < n → lpHasDomain (y_n n) (Set.Icc (-1 : ℝ) 1))
  (h5 : ∀ n : ℕ, 0 < n → ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      x ^ (2 : ℕ) + (y_n n x) ^ (2 : ℕ) = 1)
  : ∀ n : ℕ, 0 < n → lpCircleSolutionOn (y_n n) := by
  sorry

-- PROOF GAP @4
theorem proof_gap_exercise_3364_1_4
  (y : ℝ -> ℝ) (y_n : ℕ -> ℝ -> ℝ) (n : ℕ)
  (hn : 0 < n)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : ∀ n : ℕ, 0 < n → y_n n = lpYn n)
  (h4 : ∀ n : ℕ, 0 < n → lpHasDomain (y_n n) (Set.Icc (-1 : ℝ) 1))
  (h5 : ∀ n : ℕ, 0 < n → ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      x ^ (2 : ℕ) + (y_n n x) ^ (2 : ℕ) = 1)
  (h6 : ∀ n : ℕ, 0 < n → lpCircleSolutionOn (y_n n))
  : Set.Infinite {v : ℝ -> ℝ | ∃ n : ℕ, 0 < n ∧ v = y_n n} ↔ lpCircleSolutionOn y := by
  sorry
