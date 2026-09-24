import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_3237
-- Exercise 3237, gap 1
theorem proof_gap_exercise_3237_1
  (u : ℝ × ℝ -> ℝ)
  (h_u : ∀ (x y : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 →
    u (x, y) = Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
  : ∀ (x y dx dy : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 →
    ((fderiv ℝ u (x, y)) (dx, dy)) =
      (x /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dx +
      (y /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dy := by
  sorry

-- Exercise 3237, gap 2
theorem proof_gap_exercise_3237_2
  (u : ℝ × ℝ -> ℝ)
  (h_u : ∀ (x y : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 →
    u (x, y) = Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
  (h_du : ∀ (x y dx dy : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 →
    ((fderiv ℝ u (x, y)) (dx, dy)) =
      (x /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dx +
      (y /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dy)
  : ∀ (x y dx dy : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 →
    ((fderiv ℝ (fun p : ℝ × ℝ => (fderiv ℝ u p : (ℝ × ℝ) →L[ℝ] ℝ)) (x, y)) (dx, dy)) (dx, dy) =
      (y ^ (2 : ℕ) /. Real.rpow (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ((3 : ℝ) /. 2)) * dx ^ (2 : ℕ) -
      (2 * x * y /. Real.rpow (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ((3 : ℝ) /. 2)) * dx * dy +
      (x ^ (2 : ℕ) /. Real.rpow (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ((3 : ℝ) /. 2)) * dy ^ (2 : ℕ) := by
  sorry
