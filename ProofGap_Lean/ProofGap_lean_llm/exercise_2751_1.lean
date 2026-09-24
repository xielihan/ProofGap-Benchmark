import Mathlib

noncomputable section

namespace Exercise2751_1

abbrev SeqLim (u : ℕ -> ℝ) (a : ℝ) : Prop := Filter.Tendsto u Filter.atTop (nhds a)
def interval (eps : ℝ) : Set ℝ := Set.Icc 0 (1 - eps)
abbrev UniformConvergent (f : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ eps' : ℝ, eps' > 0 -> ∃ N : ℕ, ∀ n : ℕ, n > N -> ∀ x : ℝ, x ∈ s -> |f n x - g x| < eps'

-- exercise: exercise_2751_1

theorem proof_gap_exercise_2751_1_1
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (hf : ∀ x n, x ∈ interval eps -> 0 < n -> f n x = x ^ n / (1 + x ^ n))
    (hg : ∀ x, x ∈ interval eps -> g x = 0) :
    ∀ x, x ∈ interval eps -> SeqLim (fun n : ℕ => f n x) 0 := by sorry

theorem proof_gap_exercise_2751_1_2
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
    (hlim : ∀ x, x ∈ interval eps -> SeqLim (fun n : ℕ => f n x) 0)
    (hg : ∀ x, x ∈ interval eps -> g x = 0) :
    ∀ x, x ∈ interval eps -> g x = 0 := by sorry

theorem proof_gap_exercise_2751_1_3
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
    (hf : ∀ x n, x ∈ interval eps -> 0 < n -> f n x = x ^ n / (1 + x ^ n))
    (hg : ∀ x, x ∈ interval eps -> g x = 0) :
    ∀ n x, 0 < n -> x ∈ interval eps -> |f n x - g x| = x ^ n / (1 + x ^ n) := by sorry

theorem proof_gap_exercise_2751_1_4 (eps : ℝ) :
    ∀ x n, x ∈ interval eps -> 0 < n -> x ^ n / (1 + x ^ n) < (1 - eps) ^ n := by sorry

theorem proof_gap_exercise_2751_1_5
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ) :
    ∀ n x, 0 < n -> x ∈ interval eps -> |f n x - g x| < (1 - eps) ^ n := by sorry

theorem proof_gap_exercise_2751_1_6
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
    (hbound : ∀ n x, 0 < n -> x ∈ interval eps -> |f n x - g x| < (1 - eps) ^ n) :
    ∀ n x, 0 < n -> x ∈ interval eps -> ∀ eps' : ℝ, eps' > 0 -> (1 - eps) ^ n < eps' -> |f n x - g x| < eps' := by sorry

theorem proof_gap_exercise_2751_1_7 (eps : ℝ) :
    ∀ n, 0 < n -> ∀ eps' : ℝ, eps' > 0 -> (n : ℝ) > Real.log eps' / Real.log (1 - eps) -> (1 - eps) ^ n < eps' := by sorry

theorem proof_gap_exercise_2751_1_8
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < n -> x ∈ interval eps -> ∀ eps' : ℝ, eps' > 0 ->
      (n : ℝ) > Real.log eps' / Real.log (1 - eps) -> |f n x - g x| < eps' := by sorry

theorem proof_gap_exercise_2751_1_9
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ) :
    ∀ eps' : ℝ, eps' > 0 -> ∃ N : ℕ, (N : ℝ) = Nat.floor (Real.log eps' / Real.log (1 - eps)) ∧
      ∀ n x, n > N -> 0 < n -> x ∈ interval eps -> |f n x - g x| < eps' := by sorry

theorem proof_gap_exercise_2751_1_10
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
    (huc : ∀ eps' : ℝ, eps' > 0 -> ∃ N : ℕ, (N : ℝ) = Nat.floor (Real.log eps' / Real.log (1 - eps)) ∧
      ∀ n x, n > N -> 0 < n -> x ∈ interval eps -> |f n x - g x| < eps') :
    UniformConvergent f (interval eps) g := by sorry

theorem proof_gap_exercise_2751_1_11
    (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
    (huc : UniformConvergent f (interval eps) g) :
    UniformConvergent f (interval eps) g := by sorry

end Exercise2751_1
