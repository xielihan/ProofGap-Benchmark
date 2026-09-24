import Mathlib

set_option linter.style.longLine false

def DefinedOn (f : ℝ -> ℝ) (I : Set ℝ) : Prop :=
  Set.MapsTo f I Set.univ

def UniformConvergent (F : ℕ -> ℝ -> ℝ) (I : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → ∀ x : ℝ, x ∈ I → |F n x - f x| < ε

-- exercise: exercise_2742_2

theorem proof_gap_exercise_2742_2_1
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h6 : I = Set.Ioi x0)
  (h7 : ∀ n : ℕ, 0 < n → DefinedOn (F n) I)
  (h8 : DefinedOn f I)
  : ∀ a b : ℝ, Set.Ioo a b ⊆ I → ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, 0 < n ∧ n > N → ∀ x a b : ℝ, x ∈ Set.Ioo a b → |F n x - f x| < ε := by
  sorry

theorem proof_gap_exercise_2742_2_2
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h6 : I = Set.Ioi x0)
  (h7 : ∀ n : ℕ, 0 < n → DefinedOn (F n) I)
  (h8 : DefinedOn f I)
  (h9 : ∀ a b : ℝ, Set.Ioo a b ⊆ I → ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, 0 < n ∧ n > N → ∀ x a b : ℝ, x ∈ Set.Ioo a b → |F n x - f x| < ε)
  : ∃ N : ℝ -> ℝ -> ℝ -> ℕ, ∀ ε a b : ℝ, ε > 0 ∧ Set.Ioo a b ⊆ I → 0 < N ε a b := by
  sorry

theorem proof_gap_exercise_2742_2_3
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h6 : I = Set.Ioi x0)
  (h7 : ∀ n : ℕ, 0 < n → DefinedOn (F n) I)
  (h8 : DefinedOn f I)
  (h9 : ∀ a b : ℝ, Set.Ioo a b ⊆ I → ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, 0 < n ∧ n > N → ∀ x a b : ℝ, x ∈ Set.Ioo a b → |F n x - f x| < ε)
  (h10 : ∃ N : ℝ -> ℝ -> ℝ -> ℕ, ∀ ε a b : ℝ, ε > 0 ∧ Set.Ioo a b ⊆ I → 0 < N ε a b)
  : (∀ a b : ℝ, Set.Ioo a b ⊆ I → UniformConvergent F (Set.Ioo a b) f) →
      ∀ n : ℕ, 0 < n → DefinedOn (F n) I := by
  sorry
