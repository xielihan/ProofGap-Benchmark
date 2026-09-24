import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_3241
-- Exercise 3241, gap 1
theorem proof_gap_exercise_3241_1
  (u : ℝ × (ℝ × ℝ) -> ℝ)
  (h_u : ∀ (x y z : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 →
    u (x, (y, z)) = z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
  : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
    ((fderiv ℝ u (x, (y, z))) (dx, (dy, dz))) =
      (-(2 * z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ))) * (x * dx + y * dy) +
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dz := by
  sorry

-- Exercise 3241, gap 2
theorem proof_gap_exercise_3241_2
  (u : ℝ × (ℝ × ℝ) -> ℝ)
  (h_u : ∀ (x y z : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 →
    u (x, (y, z)) = z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
  (h_du : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
    ((fderiv ℝ u (x, (y, z))) (dx, (dy, dz))) =
      (-(2 * z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ))) * (x * dx + y * dy) +
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dz)
  : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
      (-(2 * z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ))) * (x * dx + y * dy) +
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dz =
        (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ)) *
          ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) * dz - (2 * z) * (x * dx + y * dy)) := by
  sorry

-- Exercise 3241, gap 3
theorem proof_gap_exercise_3241_3
  (u : ℝ × (ℝ × ℝ) -> ℝ)
  (h_u : ∀ (x y z : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 →
    u (x, (y, z)) = z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
  (h_du_first : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
    ((fderiv ℝ u (x, (y, z))) (dx, (dy, dz))) =
      (-(2 * z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ))) * (x * dx + y * dy) +
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dz)
  (h_alg : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
      (-(2 * z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ))) * (x * dx + y * dy) +
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dz =
        (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ)) *
          ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) * dz - (2 * z) * (x * dx + y * dy)))
  : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
    ((fderiv ℝ u (x, (y, z))) (dx, (dy, dz))) =
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ)) *
        ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) * dz - (2 * z) * (x * dx + y * dy)) := by
  sorry

-- Exercise 3241, gap 4
theorem proof_gap_exercise_3241_4
  (u : ℝ × (ℝ × ℝ) -> ℝ)
  (h_u : ∀ (x y z : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 →
    u (x, (y, z)) = z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
  (h_du_first : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
    ((fderiv ℝ u (x, (y, z))) (dx, (dy, dz))) =
      (-(2 * z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ))) * (x * dx + y * dy) +
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dz)
  (h_alg : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
      (-(2 * z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ))) * (x * dx + y * dy) +
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ))) * dz =
        (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ)) *
          ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) * dz - (2 * z) * (x * dx + y * dy)))
  (h_du_second : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
    ((fderiv ℝ u (x, (y, z))) (dx, (dy, dz))) =
      (1 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ)) *
        ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) * dz - (2 * z) * (x * dx + y * dy)))
  : ∀ (x y z dx dy dz : ℝ), x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 ∧ z ∈ (Set.univ : Set ℝ) →
    ((fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => (fderiv ℝ u p : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ)) (x, (y, z))) (dx, (dy, dz))) (dx, (dy, dz)) =
      (2 * z /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (3 : ℕ)) *
        ((3 * x ^ (2 : ℕ) - y ^ (2 : ℕ)) * dx ^ (2 : ℕ) +
          (8 * x * y) * dx * dy +
          (3 * y ^ (2 : ℕ) - x ^ (2 : ℕ)) * dy ^ (2 : ℕ)) -
      (4 /. (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ)) * (x * dx + y * dy) * dz := by
  sorry
