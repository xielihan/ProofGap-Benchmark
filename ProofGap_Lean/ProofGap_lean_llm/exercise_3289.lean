import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

-- exercise: exercise_3289

noncomputable def pg3289_tForm (x y : ℝ) : ℝ :=
  y / x

noncomputable def pg3289_duRhs (f : ℝ -> ℝ) (t x y dx dy : ℝ) : ℝ :=
  deriv f t * ((x * dy - y * dx) / x ^ (2 : ℕ))

noncomputable def pg3289_d2uRhs (f : ℝ -> ℝ) (t x y dx dy : ℝ) : ℝ :=
  iteratedDeriv 2 f t * ((x * dy - y * dx) ^ (2 : ℕ) / x ^ (4 : ℕ))
    - 2 * deriv f t * (dx * (x * dy - y * dx) / x ^ (3 : ℕ))

theorem proof_gap_exercise_3289_1
  (u : ℝ × ℝ -> ℝ)
  (t f : ℝ -> ℝ)
  (h_t : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ->
    t (x, y).2 = y / x)
  (h_u : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ->
    u (x, y) = f (t (x, y).2))
  (h_f : ContDiff ℝ (2 : ℕ∞) f)
  : ∀ x y dx dy : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ y ∈ (Set.univ : Set ℝ) ->
      pg3289_duRhs f (t (x, y).2) x y dx dy =
        deriv f (t (x, y).2) * ((x * dy - y * dx) / x ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_3289_2
  (u : ℝ × ℝ -> ℝ)
  (t f : ℝ -> ℝ)
  (h_t : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ->
    t (x, y).2 = y / x)
  (h_u : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ->
    u (x, y) = f (t (x, y).2))
  (h_f : ContDiff ℝ (2 : ℕ∞) f)
  (h_du : ∀ x y dx dy : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ y ∈ (Set.univ : Set ℝ) ->
      pg3289_duRhs f (t (x, y).2) x y dx dy =
        deriv f (t (x, y).2) * ((x * dy - y * dx) / x ^ (2 : ℕ)))
  : ∀ x y dx dy : ℝ,
      x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ y ∈ (Set.univ : Set ℝ) ->
      pg3289_d2uRhs f (t (x, y).2) x y dx dy =
        iteratedDeriv 2 f (t (x, y).2) * ((x * dy - y * dx) ^ (2 : ℕ) / x ^ (4 : ℕ))
          - 2 * deriv f (t (x, y).2) * (dx * (x * dy - y * dx) / x ^ (3 : ℕ)) := by
  sorry
