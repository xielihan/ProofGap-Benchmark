import Mathlib

set_option linter.style.longLine false

open scoped BigOperators

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_3128
-- Bernstein polynomial on [a,b].

theorem proof_gap_exercise_3128_1
  (a b : ℝ) (f : ℝ -> ℝ) (B : ℕ × ℝ -> ℝ)
  (hab : a < b)
  : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → a ≤ x := by
  sorry

theorem proof_gap_exercise_3128_2
  (a b : ℝ) (f : ℝ -> ℝ) (B : ℕ × ℝ -> ℝ)
  (hab : a < b)
  (h6 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → a ≤ x)
  : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → x ≤ b := by
  sorry

theorem proof_gap_exercise_3128_3
  (a b : ℝ) (f : ℝ -> ℝ) (B : ℕ × ℝ -> ℝ)
  (hab : a < b)
  (h6 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → a ≤ x)
  (h7 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → x ≤ b)
  : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → y = (x - a) /. (b - a) := by
  sorry

theorem proof_gap_exercise_3128_4
  (a b : ℝ) (f : ℝ -> ℝ) (B : ℕ × ℝ -> ℝ)
  (hab : a < b)
  (h6 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → a ≤ x)
  (h7 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → x ≤ b)
  (h8 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → y = (x - a) /. (b - a))
  : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → 1 - y = (b - x) /. (b - a) := by
  sorry

theorem proof_gap_exercise_3128_5
  (a b : ℝ) (f : ℝ -> ℝ) (B : ℕ × ℝ -> ℝ)
  (hab : a < b)
  (h6 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → a ≤ x)
  (h7 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → x ≤ b)
  (h8 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → y = (x - a) /. (b - a))
  (h9 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → 1 - y = (b - x) /. (b - a))
  : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → f x = f (a + (b - a) * y) := by
  sorry

theorem proof_gap_exercise_3128_6
  (a b : ℝ) (f : ℝ -> ℝ) (B : ℕ × ℝ -> ℝ)
  (hab : a < b)
  (h6 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → a ≤ x)
  (h7 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → x ≤ b)
  (h8 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → y = (x - a) /. (b - a))
  (h9 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → 1 - y = (b - x) /. (b - a))
  (h10 : ∀ (y x : ℝ), 0 ≤ y ∧ y ≤ 1 ∧ x = a + (b - a) * y → f x = f (a + (b - a) * y))
  : (∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Icc a b →
      B (n, x) =
        ∑ k ∈ Finset.Icc 0 n,
          f (a + (b - a) * (k /. n)) * Nat.choose n k *
            (((x - a) ^ k * (b - x) ^ (n - k)) /. ((b - a) ^ n))) →
    (∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Icc a b →
      B (n, x) =
        ∑ k ∈ Finset.Icc 0 n,
          f (a + (b - a) * (k /. n)) * Nat.choose n k *
            (((x - a) ^ k * (b - x) ^ (n - k)) /. ((b - a) ^ n))) := by
  sorry
