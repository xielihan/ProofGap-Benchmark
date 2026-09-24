import Mathlib

set_option linter.style.longLine false

-- exercise: exercise_3364_3

def lpHasDomain (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  s.Nonempty ∨ s = ∅

def lpContinuousCircleSolutionOn (y : ℝ -> ℝ) : Prop :=
  lpHasDomain y (Set.Icc (-1 : ℝ) 1) ∧ ContinuousOn y (Set.Icc (-1 : ℝ) 1) ∧
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1

noncomputable def y_pos : ℝ -> ℝ :=
  fun x => Real.sqrt (1 - x ^ (2 : ℕ))

noncomputable def y_neg : ℝ -> ℝ :=
  fun x => -Real.sqrt (1 - x ^ (2 : ℕ))

-- PROOF GAP @1
theorem proof_gap_exercise_3364_3_1
  (y : ℝ -> ℝ)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  : y_pos 0 = 1 := by
  sorry

-- PROOF GAP @2
theorem proof_gap_exercise_3364_3_2
  (y : ℝ -> ℝ)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : y_pos 0 = 1)
  : y_neg 0 = -1 := by
  sorry

-- PROOF GAP @3
theorem proof_gap_exercise_3364_3_3
  (y : ℝ -> ℝ)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : y_pos 0 = 1)
  (h4 : y_neg 0 = -1)
  : y = y_pos ↔ lpContinuousCircleSolutionOn y ∧ y 0 = 1 := by
  sorry

-- PROOF GAP @4
theorem proof_gap_exercise_3364_3_4
  (y : ℝ -> ℝ)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : y_pos 0 = 1)
  (h4 : y_neg 0 = -1)
  (h5 : y = y_pos ↔ lpContinuousCircleSolutionOn y ∧ y 0 = 1)
  : y_pos 1 = 0 := by
  sorry

-- PROOF GAP @5
theorem proof_gap_exercise_3364_3_5
  (y : ℝ -> ℝ)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : y_pos 0 = 1)
  (h4 : y_neg 0 = -1)
  (h5 : y = y_pos ↔ lpContinuousCircleSolutionOn y ∧ y 0 = 1)
  (h6 : y_pos 1 = 0)
  : y_neg 1 = 0 := by
  sorry

-- PROOF GAP @6
theorem proof_gap_exercise_3364_3_6
  (y : ℝ -> ℝ)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : y_pos 0 = 1)
  (h4 : y_neg 0 = -1)
  (h5 : y = y_pos ↔ lpContinuousCircleSolutionOn y ∧ y 0 = 1)
  (h6 : y_pos 1 = 0)
  (h7 : y_neg 1 = 0)
  : y ∈ ({y_pos, y_neg} : Set (ℝ -> ℝ)) ↔ lpContinuousCircleSolutionOn y ∧ y 1 = 0 := by
  sorry

-- PROOF GAP @7
theorem proof_gap_exercise_3364_3_7
  (y : ℝ -> ℝ)
  (h1 : lpHasDomain y (Set.Icc (-1 : ℝ) 1))
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1)
  (h3 : y_pos 0 = 1)
  (h4 : y_neg 0 = -1)
  (h5 : y = y_pos ↔ lpContinuousCircleSolutionOn y ∧ y 0 = 1)
  (h6 : y_pos 1 = 0)
  (h7 : y_neg 1 = 0)
  (h8 : y ∈ ({y_pos, y_neg} : Set (ℝ -> ℝ)) ↔ lpContinuousCircleSolutionOn y ∧ y 1 = 0)
  : ((y 0 = 1 → y = y_pos) ∧ (y 1 = 0 → y ∈ ({y_pos, y_neg} : Set (ℝ -> ℝ)))) ↔
      lpContinuousCircleSolutionOn y := by
  sorry
