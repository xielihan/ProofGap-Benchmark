import Mathlib

set_option linter.style.longLine false

def ConvergentSeqOn (F : ℕ -> ℝ -> ℝ) (I : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  ∀ ε x : ℝ, x ∈ I ∧ ε > 0 → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → |F n x - f x| < ε

-- exercise: exercise_2742_1

theorem proof_gap_exercise_2742_1_1
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h5 : I = Set.Ioi x0)
  (h6 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) I Set.univ)
  : Set.MapsTo f I Set.univ := by
  sorry

theorem proof_gap_exercise_2742_1_2
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h5 : I = Set.Ioi x0)
  (h6 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) I Set.univ)
  (h7 : Set.MapsTo f I Set.univ)
  : ∀ ε x : ℝ, ε > 0 ∧ x ∈ I → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → |F n x - f x| < ε := by
  sorry

theorem proof_gap_exercise_2742_1_3
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h5 : I = Set.Ioi x0)
  (h6 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) I Set.univ)
  (h7 : Set.MapsTo f I Set.univ)
  (h8 : ∀ ε x : ℝ, ε > 0 ∧ x ∈ I → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → |F n x - f x| < ε)
  : ∃ N : ℝ -> ℝ -> ℕ, ∀ ε x : ℝ, ε > 0 ∧ x ∈ I → 0 < N ε x := by
  sorry

theorem proof_gap_exercise_2742_1_4
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (x0 : ℝ) (I : Set ℝ)
  (h5 : I = Set.Ioi x0)
  (h6 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) I Set.univ)
  (h7 : Set.MapsTo f I Set.univ)
  (h8 : ∀ ε x : ℝ, ε > 0 ∧ x ∈ I → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → |F n x - f x| < ε)
  (h9 : ∃ N : ℝ -> ℝ -> ℕ, ∀ ε x : ℝ, ε > 0 ∧ x ∈ I → 0 < N ε x)
  : (ConvergentSeqOn F I f ↔ ∀ ε x : ℝ, ε > 0 ∧ x ∈ I → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, 0 < n ∧ n > N → |F n x - f x| < ε) →
      Set.MapsTo f I Set.univ := by
  sorry
