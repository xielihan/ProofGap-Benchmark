import Mathlib

noncomputable section

namespace Exercise3407

abbrev Point := ℝ × ℝ

variable (F u v : Point → ℝ)
variable (D : (Point → ℝ) → ℕ → ℕ → Point → ℝ)
variable (Dom : (Point → ℝ) → Set Point)

def base : Prop :=
  ∀ x y : ℝ, x = u (x, y) + v (x, y) ∧
    y = u (x, y) ^ 2 + v (x, y) ^ 2 ∧
    F (x, y) = u (x, y) ^ 3 + v (x, y) ^ 3

-- Exercise 3407, gap 1
theorem proof_gap_exercise_3407_1 (h : base F u v) :
    ∀ x y : ℝ,
      (u (x, y) = (x + Real.sqrt (2 * y - x ^ 2)) / 2 ∧
        v (x, y) = (x - Real.sqrt (2 * y - x ^ 2)) / 2) ∨
      (u (x, y) = (x - Real.sqrt (2 * y - x ^ 2)) / 2 ∧
        v (x, y) = (x + Real.sqrt (2 * y - x ^ 2)) / 2) := by sorry

-- Exercise 3407, gap 2
theorem proof_gap_exercise_3407_2 :
    ∀ y x : ℝ, 2 * y - x ^ 2 ≥ 0 := by sorry

-- Exercise 3407, gap 3
theorem proof_gap_exercise_3407_3 :
    ∀ y x : ℝ, y ≥ x ^ 2 / 2 := by sorry

-- Exercise 3407, gap 4
theorem proof_gap_exercise_3407_4 :
    Dom F = {p : Point | p.2 ≥ p.1 ^ 2 / 2} := by sorry

-- Exercise 3407, gap 5
theorem proof_gap_exercise_3407_5 :
    ∀ x y : ℝ, 1 = D u 1 1 (x, y) + D v 1 1 (x, y) := by sorry

-- Exercise 3407, gap 6
theorem proof_gap_exercise_3407_6 :
    ∀ x y : ℝ, 0 = 2 * u (x, y) * D u 1 1 (x, y) +
      2 * v (x, y) * D v 1 1 (x, y) := by sorry

-- Exercise 3407, gap 7
theorem proof_gap_exercise_3407_7 :
    ∀ x y : ℝ, D u 1 1 (x, y) = v (x, y) / (v (x, y) - u (x, y)) := by sorry

-- Exercise 3407, gap 8
theorem proof_gap_exercise_3407_8 :
    ∀ x y : ℝ, D v 1 1 (x, y) = -u (x, y) / (v (x, y) - u (x, y)) := by sorry

-- Exercise 3407, gap 9
theorem proof_gap_exercise_3407_9 :
    ∀ x y : ℝ, D F 1 1 (x, y) =
      3 * u (x, y) ^ 2 * D u 1 1 (x, y) +
      3 * v (x, y) ^ 2 * D v 1 1 (x, y) := by sorry

-- Exercise 3407, gap 10
theorem proof_gap_exercise_3407_10 :
    ∀ x y : ℝ,
      3 * u (x, y) ^ 2 * D u 1 1 (x, y) +
      3 * v (x, y) ^ 2 * D v 1 1 (x, y) =
      -3 * u (x, y) * v (x, y) := by sorry

-- Exercise 3407, gap 11
theorem proof_gap_exercise_3407_11 :
    ∀ x y : ℝ, D F 1 1 (x, y) = -3 * u (x, y) * v (x, y) := by sorry

-- Exercise 3407, gap 12
theorem proof_gap_exercise_3407_12 :
    ∀ x y : ℝ, D F 2 1 (x, y) = (3 / 2) * (u (x, y) + v (x, y)) := by sorry

-- Exercise 3407, gap 13
theorem proof_gap_exercise_3407_13 :
    ∀ x y : ℝ, x ^ 2 - y = 2 * u (x, y) * v (x, y) := by sorry

-- Exercise 3407, gap 14
theorem proof_gap_exercise_3407_14 :
    ∀ x y : ℝ, F (x, y) =
      (u (x, y) + v (x, y)) *
        (u (x, y) ^ 2 - u (x, y) * v (x, y) + v (x, y) ^ 2) := by sorry

-- Exercise 3407, gap 15
theorem proof_gap_exercise_3407_15 :
    ∀ x y : ℝ,
      (u (x, y) + v (x, y)) *
        (u (x, y) ^ 2 - u (x, y) * v (x, y) + v (x, y) ^ 2) =
      (x / 2) * (3 * y - x ^ 2) := by sorry

-- Exercise 3407, gap 16
theorem proof_gap_exercise_3407_16 :
    ∀ x y : ℝ, F (x, y) = (x / 2) * (3 * y - x ^ 2) := by sorry

-- Exercise 3407, gap 17
theorem proof_gap_exercise_3407_17 :
    ∀ x y : ℝ, D F 1 1 (x, y) = (3 / 2) * y - (3 / 2) * x ^ 2 := by sorry

-- Exercise 3407, gap 18
theorem proof_gap_exercise_3407_18 :
    ∀ x y : ℝ, D F 2 1 (x, y) = (3 / 2) * x := by sorry

-- Exercise 3407, gap 19
theorem proof_gap_exercise_3407_19 :
    ∀ x y : ℝ,
      Dom F = {p : Point | p.2 ≥ p.1 ^ 2 / 2} →
      D F 1 1 (x, y) = (3 / 2) * y - (3 / 2) * x ^ 2 →
      D F 2 1 (x, y) = (3 / 2) * x →
      ∀ x y : ℝ, (x, y) ∈ Dom F →
        ∃ u0 v0 : ℝ, x = u0 + v0 ∧ y = u0 ^ 2 + v0 ^ 2 := by sorry

end Exercise3407
