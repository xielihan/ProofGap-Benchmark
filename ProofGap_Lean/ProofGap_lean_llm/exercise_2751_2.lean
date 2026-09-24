import Mathlib

noncomputable section

namespace Exercise2751_2

abbrev SeqLim (u : ℕ -> ℝ) (a : ℝ) : Prop := Filter.Tendsto u Filter.atTop (nhds a)
def interval (eps : ℝ) : Set ℝ := Set.Icc (1 - eps) (1 + eps)
def limitPiece (eps x : ℝ) : ℝ := if x < 1 then 0 else if x = 1 then (1 : ℝ) / 2 else 1
abbrev UniformConvergent (f : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ eps' : ℝ, eps' > 0 -> ∃ N : ℕ, ∀ n : ℕ, n > N -> ∀ x : ℝ, x ∈ s -> |f n x - g x| < eps'

-- exercise: exercise_2751_2

theorem proof_gap_exercise_2751_2_1
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ) (heps : 0 < eps)
    (hf : ∀ x n, x ∈ interval eps -> 0 < n -> f n x = x ^ n / (1 + x ^ n))
    (hg : ∀ x, x ∈ interval eps -> g x = limitPiece eps x) :
    ∀ x, x ∈ interval eps -> SeqLim (fun n : ℕ => f n x) (g x) := by sorry

theorem proof_gap_exercise_2751_2_2 :
    0 < ((1 : ℝ) / 3) := by sorry

theorem proof_gap_exercise_2751_2_3
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
    (hg : ∀ x, x ∈ interval eps -> g x = limitPiece eps x) :
    ∀ x : ℝ, ∀ n : ℕ, x = (1 : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ))) -> 0 < n -> x ∈ interval eps -> g x = 0 := by sorry

theorem proof_gap_exercise_2751_2_4
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ) :
    ∀ x : ℝ, ∀ n : ℕ, x = (1 : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ))) -> 0 < n -> x ∈ interval eps ->
      |f n x - g x| = ((1 : ℝ) / 3) := by sorry

theorem proof_gap_exercise_2751_2_5 :
    ∀ x (n : ℕ) (eps eps0 : ℝ), x = (1 : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ->
      0 < n -> x ∈ interval eps -> eps0 = ((1 : ℝ) / 3) -> ((1 : ℝ) / 3) ≥ eps0 := by sorry

theorem proof_gap_exercise_2751_2_6
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) :
    ∀ x (n : ℕ) (eps eps0 : ℝ), x = (1 : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ->
      0 < n -> x ∈ interval eps -> eps0 = ((1 : ℝ) / 3) -> |f n x - g x| ≥ eps0 := by sorry

theorem proof_gap_exercise_2751_2_7
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ) :
    ¬ UniformConvergent f (interval eps) g := by sorry

theorem proof_gap_exercise_2751_2_8
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
    (h : ¬ UniformConvergent f (interval eps) g) :
    ¬ UniformConvergent f (interval eps) g := by sorry

end Exercise2751_2
