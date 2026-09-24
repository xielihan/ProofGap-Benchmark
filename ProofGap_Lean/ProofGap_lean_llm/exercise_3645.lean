import Mathlib

noncomputable section

open Set

def u3645 (a x y z : ℝ) : ℝ :=
  x * y ^ 2 * z ^ 3 * (a - x - 2 * y - 3 * z)

def IsLocalMaxAt3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : Prop :=
  ∃ r > 0, ∀ x' y' z', dist (x', y', z') (x, y, z) < r → f x' y' z' ≤ f x y z

def IsLocalMinAt3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : Prop :=
  ∃ r > 0, ∀ x' y' z', dist (x', y', z') (x, y, z) < r → f x y z ≤ f x' y' z'

def NotLocalExtremumAt3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : Prop :=
  ¬ IsLocalMaxAt3 f x y z ∧ ¬ IsLocalMinAt3 f x y z

-- Exercise 3645, gap 1
theorem proof_gap_exercise_3645_1 (a : ℝ) (ha : 0 < a) :
    ∀ x y z,
      deriv (fun t => u3645 a t y z) x =
        y ^ 2 * z ^ 3 * (a - 2 * x - 2 * y - 3 * z) := by
  sorry

-- Exercise 3645, gap 2
theorem proof_gap_exercise_3645_2 (a : ℝ) (ha : 0 < a) :
    ∀ x y z,
      deriv (fun t => u3645 a x t z) y =
        2 * x * y * z ^ 3 * (a - x - 3 * y - 3 * z) := by
  sorry

-- Exercise 3645, gap 3
theorem proof_gap_exercise_3645_3 (a : ℝ) (ha : 0 < a) :
    ∀ x y z,
      deriv (fun t => u3645 a x y t) z =
        3 * x * y ^ 2 * z ^ 2 * (a - x - 2 * y - 4 * z) := by
  sorry

-- Exercise 3645, gap 4
theorem proof_gap_exercise_3645_4 (a : ℝ) (ha : 0 < a) :
    u3645 a (a / 7) (a / 7) (a / 7) = a ^ 7 / 7 ^ 7 := by
  sorry

-- Exercise 3645, gap 5
theorem proof_gap_exercise_3645_5 (a : ℝ) (ha : 0 < a) :
    deriv (fun t => u3645 a t (a / 7) (a / 7)) (a / 7) = 0 ∧
    deriv (fun t => u3645 a (a / 7) t (a / 7)) (a / 7) = 0 ∧
    deriv (fun t => u3645 a (a / 7) (a / 7) t) (a / 7) = 0 := by
  sorry

-- Exercise 3645, gap 6
theorem proof_gap_exercise_3645_6 (a x y z : ℝ) (ha : 0 < a)
    (hx : x = 0) (hline : 2 * y + 3 * z = a) :
    deriv (fun t => u3645 a t y z) x = 0 ∧
    deriv (fun t => u3645 a x t z) y = 0 ∧
    deriv (fun t => u3645 a x y t) z = 0 := by
  sorry

-- Exercise 3645, gap 7
theorem proof_gap_exercise_3645_7 (a x z : ℝ) (ha : 0 < a) :
    deriv (fun t => u3645 a t 0 z) x = 0 ∧
    deriv (fun t => u3645 a x t z) 0 = 0 ∧
    deriv (fun t => u3645 a x 0 t) z = 0 := by
  sorry

-- Exercise 3645, gap 8
theorem proof_gap_exercise_3645_8 (a x y : ℝ) (ha : 0 < a) :
    deriv (fun t => u3645 a t y 0) x = 0 ∧
    deriv (fun t => u3645 a x t 0) y = 0 ∧
    deriv (fun t => u3645 a x y t) 0 = 0 := by
  sorry

-- Exercise 3645, gap 9
theorem proof_gap_exercise_3645_9 (a x y z : ℝ) (ha : 0 < a)
    (hcrit :
      deriv (fun t => u3645 a t y z) x = 0 ∧
      deriv (fun t => u3645 a x t z) y = 0 ∧
      deriv (fun t => u3645 a x y t) z = 0) :
    (x = a / 7 ∧ y = a / 7 ∧ z = a / 7) ∨
    (x = 0 ∧ 2 * y + 3 * z = a) ∨ y = 0 ∨ z = 0 := by
  sorry

-- Exercise 3645, gap 10
theorem proof_gap_exercise_3645_10 (a y z : ℝ) (ha : 0 < a)
    (hline : 2 * y + 3 * z = a) :
    NotLocalExtremumAt3 (u3645 a) 0 y z := by
  sorry

-- Exercise 3645, gap 11
theorem proof_gap_exercise_3645_11 (a x y : ℝ) (ha : 0 < a) :
    NotLocalExtremumAt3 (u3645 a) x y 0 := by
  sorry

-- Exercise 3645, gap 12
theorem proof_gap_exercise_3645_12 (a x z : ℝ) (ha : 0 < a)
    (hpos : x * z ^ 3 * (a - x - 3 * z) > 0) :
    IsLocalMinAt3 (u3645 a) x 0 z ∧ u3645 a x 0 z = 0 := by
  sorry

-- Exercise 3645, gap 13
theorem proof_gap_exercise_3645_13 (a x z : ℝ) (ha : 0 < a)
    (hneg : x * z ^ 3 * (a - x - 3 * z) < 0) :
    IsLocalMaxAt3 (u3645 a) x 0 z ∧ u3645 a x 0 z = 0 := by
  sorry

-- Exercise 3645, gap 14
theorem proof_gap_exercise_3645_14 (a x z : ℝ) (ha : 0 < a)
    (hzero : x * z ^ 3 * (a - x - 3 * z) = 0) :
    NotLocalExtremumAt3 (u3645 a) x 0 z := by
  sorry

-- Exercise 3645, gap 15
theorem proof_gap_exercise_3645_15 (a dx dy dz : ℝ) (ha : 0 < a) :
    -2 * a ^ 5 / 7 ^ 5 *
        (dx ^ 2 + 3 * dy ^ 2 + 6 * dz ^ 2 + 2 * dx * dy + 6 * dy * dz + 3 * dx * dz) =
      -a ^ 5 / 7 ^ 5 *
        ((dx + 2 * dy + 3 * dz) ^ 2 + dx ^ 2 + 2 * dy ^ 2 + 3 * dz ^ 2) := by
  sorry

-- Exercise 3645, gap 16
theorem proof_gap_exercise_3645_16 (a dx dy dz : ℝ) (ha : 0 < a)
    (hnonzero : dx ^ 2 + dy ^ 2 + dz ^ 2 ≠ 0) :
    -a ^ 5 / 7 ^ 5 *
        ((dx + 2 * dy + 3 * dz) ^ 2 + dx ^ 2 + 2 * dy ^ 2 + 3 * dz ^ 2) < 0 := by
  sorry

-- Exercise 3645, gap 17
theorem proof_gap_exercise_3645_17 (a : ℝ) (ha : 0 < a) :
    IsLocalMaxAt3 (u3645 a) (a / 7) (a / 7) (a / 7) := by
  sorry

-- Exercise 3645, gap 18
theorem proof_gap_exercise_3645_18 (a : ℝ) (ha : 0 < a) :
    ¬ IsLocalMinAt3 (u3645 a) (a / 7) (a / 7) (a / 7) := by
  sorry

-- Exercise 3645, gap 19
theorem proof_gap_exercise_3645_19 (a : ℝ) (ha : 0 < a) :
    (∀ x y z,
      IsLocalMaxAt3 (u3645 a) x y z →
        (x = a / 7 ∧ y = a / 7 ∧ z = a / 7) ∨
        (y = 0 ∧ x * z ^ 3 * (a - x - 3 * z) < 0)) := by
  sorry

-- Exercise 3645, gap 20
theorem proof_gap_exercise_3645_20 (a : ℝ) (ha : 0 < a) :
    (∀ x y z,
      IsLocalMinAt3 (u3645 a) x y z →
        y = 0 ∧ x * z ^ 3 * (a - x - 3 * z) > 0) := by
  sorry

-- Exercise 3645, gap 21
theorem proof_gap_exercise_3645_21 (a : ℝ) (ha : 0 < a) :
    u3645 a (a / 7) (a / 7) (a / 7) = a ^ 7 / 7 ^ 7 ∧
    IsLocalMaxAt3 (u3645 a) (a / 7) (a / 7) (a / 7) := by
  sorry

