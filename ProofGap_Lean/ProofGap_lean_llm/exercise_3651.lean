import Mathlib

noncomputable section

def F3651 (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 - 2 * x + 2 * y - 4 * z - 10

def IsImplicitLocalMaxZ (F : ℝ → ℝ → ℝ → ℝ) (x0 y0 z0 : ℝ) : Prop :=
  F x0 y0 z0 = 0 ∧ ∃ r > 0, ∀ x y z, F x y z = 0 →
    dist (x, y) (x0, y0) < r → z ≤ z0

def IsImplicitLocalMinZ (F : ℝ → ℝ → ℝ → ℝ) (x0 y0 z0 : ℝ) : Prop :=
  F x0 y0 z0 = 0 ∧ ∃ r > 0, ∀ x y z, F x y z = 0 →
    dist (x, y) (x0, y0) < r → z0 ≤ z

def NotImplicitExtremumZ (F : ℝ → ℝ → ℝ → ℝ) (x0 y0 z0 : ℝ) : Prop :=
  ¬ IsImplicitLocalMaxZ F x0 y0 z0 ∧ ¬ IsImplicitLocalMinZ F x0 y0 z0

-- Exercise 3651, gap 1
theorem proof_gap_exercise_3651_1 :
    ∀ x y z, F3651 x y z = 0 →
      (x - 1) = 0 ∧ (y + 1) = 0 ∧ z ≠ 2 →
        ∀ dx dy dz, (x - 1) * dx + (y + 1) * dy + (z - 2) * dz = 0 → dz = 0 := by
  sorry

-- Exercise 3651, gap 2
theorem proof_gap_exercise_3651_2 :
    F3651 1 (-1) 6 = 0 ∧ F3651 1 (-1) (-2) = 0 := by
  sorry

-- Exercise 3651, gap 3
theorem proof_gap_exercise_3651_3 (z : ℝ) :
    F3651 1 (-1) z = 0 → z = 6 ∨ z = -2 := by
  sorry

-- Exercise 3651, gap 4
theorem proof_gap_exercise_3651_4 :
    ∀ x y z, F3651 x y z = 0 → z ≠ 2 →
      (deriv (fun t => F3651 t y z) x = 2 * (x - 1) ∧
       deriv (fun t => F3651 x t z) y = 2 * (y + 1) ∧
       deriv (fun t => F3651 x y t) z = 2 * (z - 2)) := by
  sorry

-- Exercise 3651, gap 5
theorem proof_gap_exercise_3651_5 (x y z : ℝ) :
    F3651 x y z = 0 → z ≠ 2 →
      ((x - 1) = 0 ∧ (y + 1) = 0) →
      (z = 6 ∨ z = -2) := by
  sorry

-- Exercise 3651, gap 6
theorem proof_gap_exercise_3651_6 (dx dy dz d2z z : ℝ) :
    dx ^ 2 + dy ^ 2 + (z - 2) * d2z + dz ^ 2 = 0 →
      z = 6 → dz = 0 → d2z = -1 / 4 * (dx ^ 2 + dy ^ 2) := by
  sorry

-- Exercise 3651, gap 7
theorem proof_gap_exercise_3651_7 (dx dy : ℝ)
    (hnonzero : dx ^ 2 + dy ^ 2 ≠ 0) :
    -1 / 4 * (dx ^ 2 + dy ^ 2) < 0 := by
  sorry

-- Exercise 3651, gap 8
theorem proof_gap_exercise_3651_8 :
    IsImplicitLocalMaxZ F3651 1 (-1) 6 := by
  sorry

-- Exercise 3651, gap 9
theorem proof_gap_exercise_3651_9 (dx dy dz d2z z : ℝ) :
    dx ^ 2 + dy ^ 2 + (z - 2) * d2z + dz ^ 2 = 0 →
      z = -2 → dz = 0 → d2z = 1 / 4 * (dx ^ 2 + dy ^ 2) := by
  sorry

-- Exercise 3651, gap 10
theorem proof_gap_exercise_3651_10 (dx dy : ℝ)
    (hnonzero : dx ^ 2 + dy ^ 2 ≠ 0) :
    0 < 1 / 4 * (dx ^ 2 + dy ^ 2) := by
  sorry

-- Exercise 3651, gap 11
theorem proof_gap_exercise_3651_11 :
    IsImplicitLocalMinZ F3651 1 (-1) (-2) := by
  sorry

-- Exercise 3651, gap 12
theorem proof_gap_exercise_3651_12 :
    ∀ x y z, F3651 x y z = 0 → z = 2 →
      (x - 1) ^ 2 + (y + 1) ^ 2 = 16 := by
  sorry

-- Exercise 3651, gap 13
theorem proof_gap_exercise_3651_13 :
    ∀ x y, (x - 1) ^ 2 + (y + 1) ^ 2 < 15 →
      ∃ z, F3651 x y z = 0 ∧ z ≠ 2 := by
  sorry

-- Exercise 3651, gap 14
theorem proof_gap_exercise_3651_14 :
    ∀ x y z, F3651 x y z = 0 → z = 2 → NotImplicitExtremumZ F3651 x y z := by
  sorry

-- Exercise 3651, gap 15
theorem proof_gap_exercise_3651_15 :
    IsImplicitLocalMaxZ F3651 1 (-1) 6 ∧ IsImplicitLocalMinZ F3651 1 (-1) (-2) := by
  sorry

-- Exercise 3651, gap 16
theorem proof_gap_exercise_3651_16 :
    F3651 1 (-1) 6 = 0 ∧ F3651 1 (-1) (-2) = 0 ∧
    IsImplicitLocalMaxZ F3651 1 (-1) 6 ∧ IsImplicitLocalMinZ F3651 1 (-1) (-2) := by
  sorry
