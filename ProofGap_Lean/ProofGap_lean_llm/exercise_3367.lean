import Mathlib

/- exercise: exercise_3367
Generated only; not compiled in this round.
-/

namespace exercise_3367

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

noncomputable def branchCore (x : ℝ) : ℝ :=
  Real.sqrt ((Real.sqrt (8 * x ^ 2 + 1) - (1 + 2 * x ^ 2)) / 2)

noncomputable def sgn (x : ℝ) : ℝ := if x > 0 then 1 else if x < 0 then -1 else 0

noncomputable def branchSet : Set (ℝ -> ℝ) :=
  {fun x => branchCore x,
   fun x => - branchCore x,
   fun x => sgn x * branchCore x,
   fun x => - sgn x * branchCore x}

noncomputable def F (p : ℝ × ℝ) : ℝ :=
  (p.1 ^ 2 + p.2 ^ 2) ^ 2 - p.1 ^ 2 + p.2 ^ 2

def PartialY (_G : ℝ × ℝ -> ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * (p.1 ^ 2 + p.2 ^ 2) * 2 * p.2 + 2 * p.2

def ContinuousFuncOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop := ContinuousOn f s

-- Exercise 3367, gap 1
theorem proof_gap_exercise_3367_1
  (y : ℝ -> ℝ) (B : Set (ℝ × ℝ))
  (h1 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2)
  : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 ->
      y x ^ 2 = (-(1 + 2 * x ^ 2) + Real.sqrt (8 * x ^ 2 + 1)) / 2 ∨
      y x ^ 2 = (-(1 + 2 * x ^ 2) - Real.sqrt (8 * x ^ 2 + 1)) / 2 := by
  sorry

-- Exercise 3367, gap 2
theorem proof_gap_exercise_3367_2
  (y : ℝ -> ℝ) (B : Set (ℝ × ℝ))
  (h1 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2)
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 ->
      y x ^ 2 = (-(1 + 2 * x ^ 2) + Real.sqrt (8 * x ^ 2 + 1)) / 2 ∨
      y x ^ 2 = (-(1 + 2 * x ^ 2) - Real.sqrt (8 * x ^ 2 + 1)) / 2)
  : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> Real.sqrt (8 * x ^ 2 + 1) ≥ 1 + 2 * x ^ 2 := by
  sorry

-- Exercise 3367, gap 3
theorem proof_gap_exercise_3367_3
  (y : ℝ -> ℝ) (B : Set (ℝ × ℝ))
  (h1 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2)
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 ->
      y x ^ 2 = (-(1 + 2 * x ^ 2) + Real.sqrt (8 * x ^ 2 + 1)) / 2 ∨
      y x ^ 2 = (-(1 + 2 * x ^ 2) - Real.sqrt (8 * x ^ 2 + 1)) / 2)
  (h3 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> Real.sqrt (8 * x ^ 2 + 1) ≥ 1 + 2 * x ^ 2)
  : y ∈ branchSet := by
  sorry

-- Exercise 3367, gap 4
theorem proof_gap_exercise_3367_4
  (y : ℝ -> ℝ) (B : Set (ℝ × ℝ))
  (h1 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2)
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 ->
      y x ^ 2 = (-(1 + 2 * x ^ 2) + Real.sqrt (8 * x ^ 2 + 1)) / 2 ∨
      y x ^ 2 = (-(1 + 2 * x ^ 2) - Real.sqrt (8 * x ^ 2 + 1)) / 2)
  (h3 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> Real.sqrt (8 * x ^ 2 + 1) ≥ 1 + 2 * x ^ 2)
  (h4 : y ∈ branchSet)
  : ∀ x : ℝ, PartialY F (x, y x) = 2 * (x ^ 2 + y x ^ 2) * 2 * y x + 2 * y x := by
  sorry

-- Exercise 3367, gap 5
theorem proof_gap_exercise_3367_5
  (y : ℝ -> ℝ) (B : Set (ℝ × ℝ))
  (h1 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2)
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 ->
      y x ^ 2 = (-(1 + 2 * x ^ 2) + Real.sqrt (8 * x ^ 2 + 1)) / 2 ∨
      y x ^ 2 = (-(1 + 2 * x ^ 2) - Real.sqrt (8 * x ^ 2 + 1)) / 2)
  (h3 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> Real.sqrt (8 * x ^ 2 + 1) ≥ 1 + 2 * x ^ 2)
  (h4 : y ∈ branchSet)
  (h5 : ∀ x : ℝ, PartialY F (x, y x) = 2 * (x ^ 2 + y x ^ 2) * 2 * y x + 2 * y x)
  : ∀ x : ℝ, PartialY F (x, y x) = 0 -> y x = 0 := by
  sorry

-- Exercise 3367, gap 6
theorem proof_gap_exercise_3367_6
  (y : ℝ -> ℝ) (B : Set (ℝ × ℝ))
  (h1 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2)
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 ->
      y x ^ 2 = (-(1 + 2 * x ^ 2) + Real.sqrt (8 * x ^ 2 + 1)) / 2 ∨
      y x ^ 2 = (-(1 + 2 * x ^ 2) - Real.sqrt (8 * x ^ 2 + 1)) / 2)
  (h3 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> Real.sqrt (8 * x ^ 2 + 1) ≥ 1 + 2 * x ^ 2)
  (h4 : y ∈ branchSet)
  (h5 : ∀ x : ℝ, PartialY F (x, y x) = 2 * (x ^ 2 + y x ^ 2) * 2 * y x + 2 * y x)
  (h6 : ∀ x : ℝ, PartialY F (x, y x) = 0 -> y x = 0)
  : ∀ x : ℝ, y x = 0 -> x = 0 ∨ x = 1 ∨ x = -1 := by
  sorry

-- Exercise 3367, gap 7
theorem proof_gap_exercise_3367_7
  (y : ℝ -> ℝ) (B : Set (ℝ × ℝ))
  (h1 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2)
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 ->
      y x ^ 2 = (-(1 + 2 * x ^ 2) + Real.sqrt (8 * x ^ 2 + 1)) / 2 ∨
      y x ^ 2 = (-(1 + 2 * x ^ 2) - Real.sqrt (8 * x ^ 2 + 1)) / 2)
  (h3 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> Real.sqrt (8 * x ^ 2 + 1) ≥ 1 + 2 * x ^ 2)
  (h4 : y ∈ branchSet)
  (h5 : ∀ x : ℝ, PartialY F (x, y x) = 2 * (x ^ 2 + y x ^ 2) * 2 * y x + 2 * y x)
  (h6 : ∀ x : ℝ, PartialY F (x, y x) = 0 -> y x = 0)
  (h7 : ∀ x : ℝ, y x = 0 -> x = 0 ∨ x = 1 ∨ x = -1)
  : B = ({(0, 0), (1, 0), (-1, 0)} : Set (ℝ × ℝ)) := by
  sorry

-- Exercise 3367, gap 8
theorem proof_gap_exercise_3367_8
  (y : ℝ -> ℝ) (B : Set (ℝ × ℝ))
  (h1 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2)
  (h2 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 ->
      y x ^ 2 = (-(1 + 2 * x ^ 2) + Real.sqrt (8 * x ^ 2 + 1)) / 2 ∨
      y x ^ 2 = (-(1 + 2 * x ^ 2) - Real.sqrt (8 * x ^ 2 + 1)) / 2)
  (h3 : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> Real.sqrt (8 * x ^ 2 + 1) ≥ 1 + 2 * x ^ 2)
  (h4 : y ∈ branchSet)
  (h5 : ∀ x : ℝ, PartialY F (x, y x) = 2 * (x ^ 2 + y x ^ 2) * 2 * y x + 2 * y x)
  (h6 : ∀ x : ℝ, PartialY F (x, y x) = 0 -> y x = 0)
  (h7 : ∀ x : ℝ, y x = 0 -> x = 0 ∨ x = 1 ∨ x = -1)
  (h8 : B = ({(0, 0), (1, 0), (-1, 0)} : Set (ℝ × ℝ)))
  : B = ({(0, 0), (1, 0), (-1, 0)} : Set (ℝ × ℝ)) ∧ y ∈ branchSet ->
      (∀ x : ℝ, x ∈ Set.Icc (-1) 1 -> (x ^ 2 + y x ^ 2) ^ 2 = x ^ 2 - y x ^ 2) ∧
      ContinuousFuncOn y (Set.Icc (-1) 1) := by
  sorry

end exercise_3367
