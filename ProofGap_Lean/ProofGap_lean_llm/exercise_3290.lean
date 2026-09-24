import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

-- exercise: exercise_3290

noncomputable def pg3290_radius (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ))

noncomputable def pg3290_duRhs (f : ℝ -> ℝ) (x y dx dy : ℝ) : ℝ :=
  deriv f (pg3290_radius x y) * ((x * dx + y * dy) / pg3290_radius x y)

noncomputable def pg3290_d2uRhs (f : ℝ -> ℝ) (x y dx dy : ℝ) : ℝ :=
  iteratedDeriv 2 f (pg3290_radius x y) *
      ((x * dx + y * dy) ^ (2 : ℕ) / (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
    + deriv f (pg3290_radius x y) *
      ((y * dx - x * dy) ^ (2 : ℕ) / (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (3 : ℕ) / pg3290_radius x y)

theorem proof_gap_exercise_3290_1
  (u : ℝ × ℝ -> ℝ)
  (f : ℝ -> ℝ)
  (h_f : ContDiffOn ℝ (2 : ℕ∞) f (Set.Ioi 0))
  (h_u : ∀ x y : ℝ,
    x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 ->
      u (x, y) = f (pg3290_radius x y))
  : ∀ x y dx dy : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 ->
      pg3290_duRhs f x y dx dy =
        deriv f (pg3290_radius x y) * ((x * dx + y * dy) / pg3290_radius x y) := by
  sorry

theorem proof_gap_exercise_3290_2
  (u : ℝ × ℝ -> ℝ)
  (f : ℝ -> ℝ)
  (h_f : ContDiffOn ℝ (2 : ℕ∞) f (Set.Ioi 0))
  (h_u : ∀ x y : ℝ,
    x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 ->
      u (x, y) = f (pg3290_radius x y))
  (h_du : ∀ x y dx dy : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 ->
      pg3290_duRhs f x y dx dy =
        deriv f (pg3290_radius x y) * ((x * dx + y * dy) / pg3290_radius x y))
  : ∀ x y dx dy : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ^ (2 : ℕ) + y ^ (2 : ℕ) > 0 ->
      pg3290_d2uRhs f x y dx dy =
        iteratedDeriv 2 f (pg3290_radius x y) *
            ((x * dx + y * dy) ^ (2 : ℕ) / (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
          + deriv f (pg3290_radius x y) *
            ((y * dx - x * dy) ^ (2 : ℕ) / (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (3 : ℕ) / pg3290_radius x y) := by
  sorry
