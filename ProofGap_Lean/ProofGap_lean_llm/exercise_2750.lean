import Mathlib

noncomputable section

namespace Exercise2750

abbrev SeqLim (u : ℕ -> ℝ) (a : ℝ) : Prop := Filter.Tendsto u Filter.atTop (nhds a)
abbrev Icc01 : Set ℝ := Set.Icc 0 1
abbrev UniformConvergent (f : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ eps : ℝ, eps > 0 -> ∃ N : ℕ, ∀ n : ℕ, n > N -> ∀ x : ℝ, x ∈ s -> |f n x - g x| < eps

-- exercise: exercise_2750

theorem proof_gap_exercise_2750_1
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ)
    (hf : ∀ x n, x ∈ Icc01 -> 0 < n -> f n x = ((n : ℝ) * x) / (1 + (n : ℝ) + x))
    (hg : ∀ x, x ∈ Icc01 -> g x = x) :
    ∀ x, x ∈ Icc01 -> SeqLim (fun n : ℕ => f n x) x := by sorry

theorem proof_gap_exercise_2750_2
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ)
    (hf : ∀ x n, x ∈ Icc01 -> 0 < n -> f n x = ((n : ℝ) * x) / (1 + (n : ℝ) + x))
    (hg : ∀ x, x ∈ Icc01 -> g x = x)
    (hlim : ∀ x, x ∈ Icc01 -> SeqLim (fun n : ℕ => f n x) x) :
    ∀ x, x ∈ Icc01 -> g x = x := by sorry

theorem proof_gap_exercise_2750_3
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ)
    (hf : ∀ x n, x ∈ Icc01 -> 0 < n -> f n x = ((n : ℝ) * x) / (1 + (n : ℝ) + x))
    (hg : ∀ x, x ∈ Icc01 -> g x = x) :
    ∀ n x, 0 < n -> x ∈ Icc01 -> |f n x - g x| = |((n : ℝ) * x) / (1 + (n : ℝ) + x) - x| := by sorry

theorem proof_gap_exercise_2750_4 :
    ∀ n x, 0 < n -> x ∈ Icc01 ->
      |((n : ℝ) * x) / (1 + (n : ℝ) + x) - x| = (x + x ^ 2) / (1 + (n : ℝ) + x) := by sorry

theorem proof_gap_exercise_2750_5 :
    ∀ x n, x ∈ Icc01 -> 0 < n -> (x + x ^ 2) / (1 + (n : ℝ) + x) < (2 : ℝ) / ((n : ℝ) + 1) := by sorry

theorem proof_gap_exercise_2750_6 :
    ∀ n, 0 < n -> (2 : ℝ) / ((n : ℝ) + 1) < (2 : ℝ) / (n : ℝ) := by sorry

theorem proof_gap_exercise_2750_7
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < n -> x ∈ Icc01 -> |f n x - g x| < (2 : ℝ) / (n : ℝ) := by sorry

theorem proof_gap_exercise_2750_8
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ)
    (hbound : ∀ n : ℕ, ∀ x : ℝ, 0 < n -> x ∈ Icc01 -> |f n x - g x| < (2 : ℝ) / (n : ℝ)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < n -> x ∈ Icc01 -> ∀ eps : ℝ, eps > 0 -> (n : ℝ) > (2 : ℝ) / eps -> |f n x - g x| < eps := by sorry

theorem proof_gap_exercise_2750_9
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ)
    (hbound : ∀ n : ℕ, ∀ x : ℝ, 0 < n -> x ∈ Icc01 -> ∀ eps : ℝ, eps > 0 -> (n : ℝ) > (2 : ℝ) / eps -> |f n x - g x| < eps) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < n -> x ∈ Icc01 -> ∀ eps : ℝ, eps > 0 -> (n : ℝ) > (2 : ℝ) / eps -> |f n x - g x| < eps := by sorry

theorem proof_gap_exercise_2750_10
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ)
    (hg : ∀ x, x ∈ Icc01 -> g x = x)
    (hexN : ∀ eps : ℝ, eps > 0 -> ∃ N : ℕ, (N : ℝ) = Nat.floor ((2 : ℝ) / eps)) :
    ∀ eps : ℝ, eps > 0 -> ∃ N : ℕ, (N : ℝ) = Nat.floor ((2 : ℝ) / eps) ∧
      ∀ n x, n > N -> 0 < n -> x ∈ Icc01 -> |f n x - g x| = |f n x - x| := by sorry

theorem proof_gap_exercise_2750_11
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) :
    ∀ eps : ℝ, eps > 0 -> ∃ N : ℕ, (N : ℝ) = Nat.floor ((2 : ℝ) / eps) ∧
      ∀ n x, n > N -> 0 < n -> x ∈ Icc01 -> |f n x - x| < eps := by sorry

theorem proof_gap_exercise_2750_12
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) :
    ∀ eps : ℝ, eps > 0 -> ∃ N : ℕ, (N : ℝ) = Nat.floor ((2 : ℝ) / eps) ∧
      ∀ n x, n > N -> 0 < n -> x ∈ Icc01 -> |f n x - g x| < eps := by sorry

theorem proof_gap_exercise_2750_13
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ)
    (huc : ∀ eps : ℝ, eps > 0 -> ∃ N : ℕ, (N : ℝ) = Nat.floor ((2 : ℝ) / eps) ∧
      ∀ n x, n > N -> 0 < n -> x ∈ Icc01 -> |f n x - g x| < eps) :
    UniformConvergent f Icc01 g := by sorry

theorem proof_gap_exercise_2750_14
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ)
    (huc : UniformConvergent f Icc01 g) :
    UniformConvergent f Icc01 g := by sorry

end Exercise2750
