import Mathlib

noncomputable section

namespace Exercise2749

abbrev SeqLim (u : ℕ → ℝ) (a : ℝ) : Prop := Filter.Tendsto u Filter.atTop (nhds a)
abbrev Ioi0 : Set ℝ := Set.Ioi 0
abbrev UniformConvergent (f : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, ∀ n : ℕ, n > N → ∀ x : ℝ, x ∈ s → |f n x - g x| < eps

-- Exercise 2749, gap 1
theorem proof_gap_exercise_2749_1
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0) :
    ∀ x : ℝ, 0 < x → SeqLim (fun n : ℕ => f n x) 0 := by
  sorry

-- Exercise 2749, gap 2
theorem proof_gap_exercise_2749_2
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hlim : ∀ x : ℝ, 0 < x → SeqLim (fun n : ℕ => f n x) 0) :
    ∀ x : ℝ, 0 < x → g x = 0 := by
  sorry

-- Exercise 2749, gap 3
theorem proof_gap_exercise_2749_3
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hlim : ∀ x : ℝ, 0 < x → SeqLim (fun n : ℕ => f n x) 0)
    (hg0 : ∀ x : ℝ, 0 < x → g x = 0) :
    ∀ n x, 0 < n → 0 < x → |f n x - g x| = (1 : ℝ) / (x + n) := by
  sorry

-- Exercise 2749, gap 4
theorem proof_gap_exercise_2749_4
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hlim : ∀ x : ℝ, 0 < x → SeqLim (fun n : ℕ => f n x) 0)
    (hg0 : ∀ x : ℝ, 0 < x → g x = 0)
    (habseq : ∀ n x, 0 < n → 0 < x → |f n x - g x| = (1 : ℝ) / (x + n)) :
    ∀ x n, 0 < x → 0 < n → (1 : ℝ) / (x + n) < (1 : ℝ) / n := by
  sorry

-- Exercise 2749, gap 5
theorem proof_gap_exercise_2749_5
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hlim : ∀ x : ℝ, 0 < x → SeqLim (fun n : ℕ => f n x) 0)
    (hg0 : ∀ x : ℝ, 0 < x → g x = 0)
    (habseq : ∀ n x, 0 < n → 0 < x → |f n x - g x| = (1 : ℝ) / (x + n))
    (hbound : ∀ x n, 0 < x → 0 < n → (1 : ℝ) / (x + n) < (1 : ℝ) / n) :
    ∀ n x, 0 < n → 0 < x → |f n x - g x| < (1 : ℝ) / n := by
  sorry

-- Exercise 2749, gap 6
theorem proof_gap_exercise_2749_6
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hsmall : ∀ n : ℕ, ∀ x : ℝ, 0 < n → 0 < x → |f n x - g x| < (1 : ℝ) / (n : ℝ)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < n → 0 < x → ∀ eps : ℝ, eps > 0 → (1 : ℝ) / (n : ℝ) < eps → |f n x - g x| < eps := by
  sorry

-- Exercise 2749, gap 7
theorem proof_gap_exercise_2749_7
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0) :
    ∀ n : ℕ, 0 < n → ∀ eps : ℝ, eps > 0 → (n : ℝ) > (1 : ℝ) / eps → (1 : ℝ) / (n : ℝ) < eps := by
  sorry

-- Exercise 2749, gap 8
theorem proof_gap_exercise_2749_8
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hsmall : ∀ n : ℕ, ∀ x : ℝ, 0 < n → 0 < x → ∀ eps : ℝ, eps > 0 → (1 : ℝ) / (n : ℝ) < eps → |f n x - g x| < eps)
    (hn : ∀ n : ℕ, 0 < n → ∀ eps : ℝ, eps > 0 → (n : ℝ) > (1 : ℝ) / eps → (1 : ℝ) / (n : ℝ) < eps) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < n → 0 < x → ∀ eps : ℝ, eps > 0 → (n : ℝ) > (1 : ℝ) / eps → |f n x - g x| < eps := by
  sorry

-- Exercise 2749, gap 9
theorem proof_gap_exercise_2749_9
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hexN : ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, (N : ℝ) = Nat.floor ((1 : ℝ) / eps)) :
    ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, (N : ℝ) = Nat.floor ((1 : ℝ) / eps) ∧
      ∀ n x, n > N → 0 < n → 0 < x → |f n x - g x| = |f n x - 0| := by
  sorry

-- Exercise 2749, gap 10
theorem proof_gap_exercise_2749_10
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hN : ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, (N : ℝ) = Nat.floor ((1 : ℝ) / eps) ∧
      ∀ n x, n > N → 0 < n → 0 < x → |f n x - g x| = |f n x - 0|) :
    ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, (N : ℝ) = Nat.floor ((1 : ℝ) / eps) ∧
      ∀ n x, n > N → 0 < n → 0 < x → |f n x - 0| < eps := by
  sorry

-- Exercise 2749, gap 11
theorem proof_gap_exercise_2749_11
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (hN0 : ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, (N : ℝ) = Nat.floor ((1 : ℝ) / eps) ∧
      ∀ n x, n > N → 0 < n → 0 < x → |f n x - g x| = |f n x - 0|)
    (hN1 : ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, (N : ℝ) = Nat.floor ((1 : ℝ) / eps) ∧
      ∀ n x, n > N → 0 < n → 0 < x → |f n x - 0| < eps) :
    ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, (N : ℝ) = Nat.floor ((1 : ℝ) / eps) ∧
      ∀ n x, n > N → 0 < n → 0 < x → |f n x - g x| < eps := by
  sorry

-- Exercise 2749, gap 12
theorem proof_gap_exercise_2749_12
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (huc : ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, (N : ℝ) = Nat.floor ((1 : ℝ) / eps) ∧
      ∀ n x, n > N → 0 < n → 0 < x → |f n x - g x| < eps) :
    UniformConvergent f Ioi0 g := by
  sorry

-- Exercise 2749, gap 13
theorem proof_gap_exercise_2749_13
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n x, 0 < n → 0 < x → f n x = (1 : ℝ) / (x + n))
    (hg : ∀ x, 0 < x → g x = 0)
    (huc : UniformConvergent f Ioi0 g) :
    UniformConvergent f Ioi0 g := by
  sorry

end Exercise2749
