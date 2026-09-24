import Mathlib

set_option linter.style.longLine false

open scoped BigOperators

noncomputable def lpPartialDeriv (coord : Nat) (f : ℝ × ℝ -> ℝ) : ℝ × ℝ -> ℝ :=
  fun p => fderiv ℝ f p (if coord = 1 then (1, 0) else (0, 1))

noncomputable def lpFunDeri (f : ℝ × ℝ -> ℝ) (coord order : Nat) : ℝ × ℝ -> ℝ :=
  Nat.iterate (lpPartialDeriv coord) order f

-- exercise: exercise_3262
-- Exercise 3262, gap 1
theorem proof_gap_exercise_3262_1
  (u : ℝ × ℝ -> ℝ)
  (x₀ y₀ : ℝ)
  (p q : Nat)
  (hp_nonneg : p ∈ (Set.univ : Set Nat))
  (hp_pos : p ∈ {n : Nat | 0 < n})
  (hq_nonneg : q ∈ (Set.univ : Set Nat))
  (hq_pos : q ∈ {n : Nat | 0 < n})
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
    u (x, y) = (x - x₀) ^ p * (y - y₀) ^ q)
  : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
    lpFunDeri u 1 p (x, y) = (Nat.factorial p : ℝ) * (y - y₀) ^ q := by
  sorry

-- Exercise 3262, gap 2
theorem proof_gap_exercise_3262_2
  (u : ℝ × ℝ -> ℝ)
  (x₀ y₀ : ℝ)
  (p q : Nat)
  (hp_nonneg : p ∈ (Set.univ : Set Nat))
  (hp_pos : p ∈ {n : Nat | 0 < n})
  (hq_nonneg : q ∈ (Set.univ : Set Nat))
  (hq_pos : q ∈ {n : Nat | 0 < n})
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
    u (x, y) = (x - x₀) ^ p * (y - y₀) ^ q)
  (hpx : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
    lpFunDeri u 1 p (x, y) = (Nat.factorial p : ℝ) * (y - y₀) ^ q)
  : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
    lpFunDeri (lpFunDeri u 1 p) 2 q (x, y) = (Nat.factorial p : ℝ) * (Nat.factorial q : ℝ) := by
  sorry

-- Exercise 3262, gap 3
theorem proof_gap_exercise_3262_3
  (u : ℝ × ℝ -> ℝ)
  (x₀ y₀ : ℝ)
  (p q : Nat)
  (hp_nonneg : p ∈ (Set.univ : Set Nat))
  (hp_pos : p ∈ {n : Nat | 0 < n})
  (hq_nonneg : q ∈ (Set.univ : Set Nat))
  (hq_pos : q ∈ {n : Nat | 0 < n})
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
    u (x, y) = (x - x₀) ^ p * (y - y₀) ^ q)
  (hpx : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
    lpFunDeri u 1 p (x, y) = (Nat.factorial p : ℝ) * (y - y₀) ^ q)
  (hpxy : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
    lpFunDeri (lpFunDeri u 1 p) 2 q (x, y) = (Nat.factorial p : ℝ) * (Nat.factorial q : ℝ))
  : lpFunDeri (lpFunDeri u 1 p) 2 q =
    (fun pxy : ℝ × ℝ => (Nat.factorial p : ℝ) * (Nat.factorial q : ℝ)) := by
  sorry
