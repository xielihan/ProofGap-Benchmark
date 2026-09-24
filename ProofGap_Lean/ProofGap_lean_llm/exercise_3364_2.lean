import Mathlib

set_option linter.style.longLine false

-- exercise: exercise_3364_2

def lpHasDomain (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  s.Nonempty ∨ s = ∅

def lpCircleSolutionOn (y : ℝ -> ℝ) : Prop :=
  lpHasDomain y (Set.Icc (-1 : ℝ) 1) ∧
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1

def lpContinuousCircleSolutionOn (y : ℝ -> ℝ) : Prop :=
  lpHasDomain y (Set.Icc (-1 : ℝ) 1) ∧ ContinuousOn y (Set.Icc (-1 : ℝ) 1) ∧
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y x) ^ (2 : ℕ) = 1

noncomputable def y_pos : ℝ -> ℝ :=
  fun x => Real.sqrt (1 - x ^ (2 : ℕ))

noncomputable def y_neg : ℝ -> ℝ :=
  fun x => -Real.sqrt (1 - x ^ (2 : ℕ))

-- PROOF GAP @1
theorem proof_gap_exercise_3364_2_1
  (y : ℝ -> ℝ)
  (h1 : lpCircleSolutionOn y)
  : ContinuousOn y_pos (Set.Icc (-1 : ℝ) 1) := by
  sorry

-- PROOF GAP @2
theorem proof_gap_exercise_3364_2_2
  (y : ℝ -> ℝ)
  (h1 : lpCircleSolutionOn y)
  (h2 : ContinuousOn y_pos (Set.Icc (-1 : ℝ) 1))
  : ContinuousOn y_neg (Set.Icc (-1 : ℝ) 1) := by
  sorry

-- PROOF GAP @3
theorem proof_gap_exercise_3364_2_3
  (y : ℝ -> ℝ)
  (h1 : lpCircleSolutionOn y)
  (h2 : ContinuousOn y_pos (Set.Icc (-1 : ℝ) 1))
  (h3 : ContinuousOn y_neg (Set.Icc (-1 : ℝ) 1))
  : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y_pos x) ^ (2 : ℕ) = 1 := by
  sorry

-- PROOF GAP @4
theorem proof_gap_exercise_3364_2_4
  (y : ℝ -> ℝ)
  (h1 : lpCircleSolutionOn y)
  (h2 : ContinuousOn y_pos (Set.Icc (-1 : ℝ) 1))
  (h3 : ContinuousOn y_neg (Set.Icc (-1 : ℝ) 1))
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y_pos x) ^ (2 : ℕ) = 1)
  : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y_neg x) ^ (2 : ℕ) = 1 := by
  sorry

-- PROOF GAP @5
theorem proof_gap_exercise_3364_2_5
  (y : ℝ -> ℝ)
  (h1 : lpCircleSolutionOn y)
  (h2 : ContinuousOn y_pos (Set.Icc (-1 : ℝ) 1))
  (h3 : ContinuousOn y_neg (Set.Icc (-1 : ℝ) 1))
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y_pos x) ^ (2 : ℕ) = 1)
  (h5 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x ^ (2 : ℕ) + (y_neg x) ^ (2 : ℕ) = 1)
  : y ∈ ({y_pos, y_neg} : Set (ℝ -> ℝ)) ↔ lpContinuousCircleSolutionOn y := by
  sorry
