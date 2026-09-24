import Mathlib

set_option linter.style.longLine false

def DefinedOn (f : ℝ -> ℝ) (I : Set ℝ) : Prop :=
  Set.MapsTo f I Set.univ

def UniformConvergent (F : ℕ -> ℝ -> ℝ) (I : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → ∀ x : ℝ, x ∈ I → |F n x - f x| < ε

-- exercise: exercise_2742_3

theorem proof_gap_exercise_2742_3_1
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h5 : I = Set.Ioi x0)
  (h6 : ∀ n : ℕ, 0 < n → DefinedOn (F n) I)
  (h7 : DefinedOn f I)
  : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → ∀ x : ℝ, x ∈ I → |F n x - f x| < ε := by
  sorry

theorem proof_gap_exercise_2742_3_2
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h5 : I = Set.Ioi x0)
  (h6 : ∀ n : ℕ, 0 < n → DefinedOn (F n) I)
  (h7 : DefinedOn f I)
  (h8 : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → ∀ x : ℝ, x ∈ I → |F n x - f x| < ε)
  : ∃ N : ℝ -> ℕ, ∀ ε : ℝ, ε > 0 → 0 < N ε := by
  sorry

theorem proof_gap_exercise_2742_3_3
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h5 : I = Set.Ioi x0)
  (h6 : ∀ n : ℕ, 0 < n → DefinedOn (F n) I)
  (h7 : DefinedOn f I)
  (h8 : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → ∀ x : ℝ, x ∈ I → |F n x - f x| < ε)
  (h9 : ∃ N : ℝ -> ℕ, ∀ ε : ℝ, ε > 0 → 0 < N ε)
  : UniformConvergent F I f → ∀ n : ℕ, 0 < n → DefinedOn (F n) I := by
  sorry
