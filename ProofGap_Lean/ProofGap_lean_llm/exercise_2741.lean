import Mathlib

set_option linter.style.longLine false

open scoped Topology
open Filter

def UniformConvergent (F : ℕ -> ℝ -> ℝ) (X : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε

noncomputable def supGamma (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (n : ℕ) : ℝ :=
  sSup (gamma n '' X)

-- exercise: exercise_2741

theorem proof_gap_exercise_2741_1
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε := by
  sorry

theorem proof_gap_exercise_2741_2
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε := by
  sorry

theorem proof_gap_exercise_2741_3
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε := by
  sorry

theorem proof_gap_exercise_2741_4
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  (h15 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε)
  : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2741_5
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  (h15 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε)
  (h16 : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0))
  : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2741_6
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  (h15 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε)
  (h16 h17 : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n < ε := by
  sorry

theorem proof_gap_exercise_2741_7
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  (h15 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε)
  (h16 h17 : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0))
  (h18 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n < ε)
  : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε := by
  sorry

theorem proof_gap_exercise_2741_8
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  (h15 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε)
  (h16 h17 : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0))
  (h18 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n < ε)
  (h19 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → UniformConvergent F X f := by
  sorry

theorem proof_gap_exercise_2741_9
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  (h15 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε)
  (h16 h17 : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0))
  (h18 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n < ε)
  (h19 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h20 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → UniformConvergent F X f)
  : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → UniformConvergent F X f := by
  sorry

theorem proof_gap_exercise_2741_10
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  (h15 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε)
  (h16 h17 : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0))
  (h18 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n < ε)
  (h19 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h20 h21 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → UniformConvergent F X f)
  : UniformConvergent F X f ↔ Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2741_11
  (F : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (gamma : ℕ -> ℝ -> ℝ) (X : Set ℝ) (a b : ℝ)
  (h8 : a < b) (h9 : X = Set.Ioo a b)
  (h10 : ∀ n : ℕ, 0 < n → Set.MapsTo (F n) X Set.univ)
  (h11 : Set.MapsTo f X Set.univ)
  (h12 : ∀ n x, 0 < n ∧ x ∈ X → gamma n x = |f x - F n x|)
  (h13 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h14 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → gamma n x < ε)
  (h15 : UniformConvergent F X f → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n ≤ ε)
  (h16 h17 : UniformConvergent F X f → Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0))
  (h18 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → supGamma gamma X n < ε)
  (h19 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → ∀ ε : ℝ, ε > 0 → ∃ N : ℤ, N > 0 ∧ ∀ n : ℕ, 0 < n ∧ (n : ℤ) > N → ∀ x : ℝ, x ∈ X → |F n x - f x| < ε)
  (h20 h21 : Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) → UniformConvergent F X f)
  (h22 : UniformConvergent F X f ↔ Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0))
  : UniformConvergent F X f ↔ Tendsto (fun n : ℕ => supGamma gamma X n) atTop (𝓝 0) := by
  sorry
