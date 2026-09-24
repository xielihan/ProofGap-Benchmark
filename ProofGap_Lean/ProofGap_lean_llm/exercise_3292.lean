import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

-- exercise: exercise_3292

noncomputable def pg3292_s (x y z : ℝ) : ℝ :=
  x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)

noncomputable def pg3292_duRhs (f : ℝ -> ℝ) (x y z dx dy dz : ℝ) : ℝ :=
  2 * deriv f (pg3292_s x y z) * (x * dx + y * dy + z * dz)

noncomputable def pg3292_d2uRhs (f : ℝ -> ℝ) (x y z dx dy dz : ℝ) : ℝ :=
  4 * iteratedDeriv 2 f (pg3292_s x y z) * (x * dx + y * dy + z * dz) ^ (2 : ℕ)
    + 2 * deriv f (pg3292_s x y z) * (dx ^ (2 : ℕ) + dy ^ (2 : ℕ) + dz ^ (2 : ℕ))

theorem proof_gap_exercise_3292_1
  (u : ℝ × ℝ × ℝ -> ℝ)
  (f : ℝ -> ℝ)
  (I : Set ℝ)
  (hI : I ⊆ (Set.univ : Set ℝ))
  (h_f : ContDiffOn ℝ (2 : ℕ∞) f I)
  (h_u : ∀ x y z : ℝ,
    x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ pg3292_s x y z ∈ I ->
      u (x, y, z) = f (pg3292_s x y z))
  : ∀ x y z dx dy dz : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ pg3292_s x y z ∈ I ->
      pg3292_duRhs f x y z dx dy dz =
        2 * deriv f (pg3292_s x y z) * (x * dx + y * dy + z * dz) := by
  sorry

theorem proof_gap_exercise_3292_2
  (u : ℝ × ℝ × ℝ -> ℝ)
  (f : ℝ -> ℝ)
  (I : Set ℝ)
  (hI : I ⊆ (Set.univ : Set ℝ))
  (h_f : ContDiffOn ℝ (2 : ℕ∞) f I)
  (h_u : ∀ x y z : ℝ,
    x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ pg3292_s x y z ∈ I ->
      u (x, y, z) = f (pg3292_s x y z))
  (h_du : ∀ x y z dx dy dz : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ pg3292_s x y z ∈ I ->
      pg3292_duRhs f x y z dx dy dz =
        2 * deriv f (pg3292_s x y z) * (x * dx + y * dy + z * dz))
  : ∀ x y z dx dy dz : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z ∈ (Set.univ : Set ℝ) ∧ pg3292_s x y z ∈ I ->
      pg3292_d2uRhs f x y z dx dy dz =
        4 * iteratedDeriv 2 f (pg3292_s x y z) * (x * dx + y * dy + z * dz) ^ (2 : ℕ)
          + 2 * deriv f (pg3292_s x y z) * (dx ^ (2 : ℕ) + dy ^ (2 : ℕ) + dz ^ (2 : ℕ)) := by
  sorry
