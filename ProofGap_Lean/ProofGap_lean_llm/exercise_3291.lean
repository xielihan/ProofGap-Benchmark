import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

-- exercise: exercise_3291

noncomputable def pg3291_t (x y z : ℝ) : ℝ :=
  x * y * z

noncomputable def pg3291_duRhs (f : ℝ -> ℝ) (x y z dx dy dz : ℝ) : ℝ :=
  deriv f (pg3291_t x y z) * (y * z * dx + x * z * dy + x * y * dz)

noncomputable def pg3291_d2uRhs (f : ℝ -> ℝ) (x y z dx dy dz : ℝ) : ℝ :=
  iteratedDeriv 2 f (pg3291_t x y z) *
      (y * z * dx + x * z * dy + x * y * dz) ^ (2 : ℕ)
    + 2 * deriv f (pg3291_t x y z) * (z * dx * dy + y * dx * dz + x * dy * dz)

theorem proof_gap_exercise_3291_1
  (u : ℝ × ℝ × ℝ -> ℝ)
  (t f : ℝ -> ℝ)
  (h_f : ContDiff ℝ (2 : ℕ∞) f)
  (h_t : ∀ x y z : ℝ,
    x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ->
      t (pg3291_t x y z) = x * y * z)
  (h_u : ∀ x y z : ℝ,
    x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ->
      u (x, y, z) = f (t (pg3291_t x y z)))
  : ∀ x y z dx dy dz : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ->
      pg3291_duRhs f x y z dx dy dz =
        deriv f (pg3291_t x y z) * (y * z * dx + x * z * dy + x * y * dz) := by
  sorry

theorem proof_gap_exercise_3291_2
  (u : ℝ × ℝ × ℝ -> ℝ)
  (t f : ℝ -> ℝ)
  (h_f : ContDiff ℝ (2 : ℕ∞) f)
  (h_t : ∀ x y z : ℝ,
    x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ->
      t (pg3291_t x y z) = x * y * z)
  (h_u : ∀ x y z : ℝ,
    x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ->
      u (x, y, z) = f (t (pg3291_t x y z)))
  (h_du : ∀ x y z dx dy dz : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ->
      pg3291_duRhs f x y z dx dy dz =
        deriv f (pg3291_t x y z) * (y * z * dx + x * z * dy + x * y * dz))
  : ∀ x y z dx dy dz : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ->
      pg3291_d2uRhs f x y z dx dy dz =
        iteratedDeriv 2 f (pg3291_t x y z) *
            (y * z * dx + x * z * dy + x * y * dz) ^ (2 : ℕ)
          + 2 * deriv f (pg3291_t x y z) * (z * dx * dy + y * dx * dz + x * dy * dz) := by
  sorry
