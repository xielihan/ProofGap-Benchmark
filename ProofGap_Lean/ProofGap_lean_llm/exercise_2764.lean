import Mathlib

set_option linter.style.longLine false

def lpUniformConvergentOn (F : ℕ × ℝ -> ℝ) (s : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n > N -> ∀ x : ℝ, x ∈ s -> |F (n, x) - f x| < ε

-- exercise: exercise_2764

theorem proof_gap_exercise_2764_1
  (F : ℕ × ℝ -> ℝ) (f : ℝ -> ℝ) (a b : ℝ)
  (hab : a < b)
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
    F (n, x) = (Int.floor ((n : ℝ) * f x) : ℝ) / (n : ℝ))
  : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
      |F (n, x) - f x| =
        (1 / (n : ℝ)) * |(Int.floor ((n : ℝ) * f x) : ℝ) - (n : ℝ) * f x| := by
  sorry

theorem proof_gap_exercise_2764_2
  (F : ℕ × ℝ -> ℝ) (f : ℝ -> ℝ) (a b : ℝ)
  (hab : a < b)
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
    F (n, x) = (Int.floor ((n : ℝ) * f x) : ℝ) / (n : ℝ))
  (h1 : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
      |F (n, x) - f x| =
        (1 / (n : ℝ)) * |(Int.floor ((n : ℝ) * f x) : ℝ) - (n : ℝ) * f x|)
  : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
      (1 / (n : ℝ)) * |(Int.floor ((n : ℝ) * f x) : ℝ) - (n : ℝ) * f x| ≤
        1 / (n : ℝ) := by
  sorry

theorem proof_gap_exercise_2764_3
  (F : ℕ × ℝ -> ℝ) (f : ℝ -> ℝ) (a b : ℝ)
  (hab : a < b)
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
    F (n, x) = (Int.floor ((n : ℝ) * f x) : ℝ) / (n : ℝ))
  (h1 : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
      |F (n, x) - f x| =
        (1 / (n : ℝ)) * |(Int.floor ((n : ℝ) * f x) : ℝ) - (n : ℝ) * f x|)
  (h2 : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
      (1 / (n : ℝ)) * |(Int.floor ((n : ℝ) * f x) : ℝ) - (n : ℝ) * f x| ≤
        1 / (n : ℝ))
  : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
      |F (n, x) - f x| ≤ 1 / (n : ℝ) := by
  sorry

theorem proof_gap_exercise_2764_4
  (F : ℕ × ℝ -> ℝ) (f : ℝ -> ℝ) (a b : ℝ)
  (hab : a < b)
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
    F (n, x) = (Int.floor ((n : ℝ) * f x) : ℝ) / (n : ℝ))
  (h3 : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
      |F (n, x) - f x| ≤ 1 / (n : ℝ))
  (hN_exists : ∀ ε : ℝ, ε > 0 -> ∃ N : ℕ, (N : ℝ) = Int.floor (1 / ε))
  : ∀ (ε : ℝ) (N n : ℕ), ε > 0 -> (N : ℝ) = Int.floor (1 / ε) ->
      n > N -> 0 < n -> ∀ x : ℝ, x ∈ Set.Icc a b -> |F (n, x) - f x| < ε := by
  sorry

theorem proof_gap_exercise_2764_5
  (F : ℕ × ℝ -> ℝ) (f : ℝ -> ℝ) (a b : ℝ)
  (hab : a < b)
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
    F (n, x) = (Int.floor ((n : ℝ) * f x) : ℝ) / (n : ℝ))
  (h4 : ∀ (ε : ℝ) (N n : ℕ), ε > 0 -> (N : ℝ) = Int.floor (1 / ε) ->
      n > N -> 0 < n -> ∀ x : ℝ, x ∈ Set.Icc a b -> |F (n, x) - f x| < ε)
  : lpUniformConvergentOn F (Set.Icc a b) f := by
  sorry

theorem proof_gap_exercise_2764_6
  (F : ℕ × ℝ -> ℝ) (f : ℝ -> ℝ) (a b : ℝ)
  (hab : a < b)
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n -> x ∈ Set.Icc a b ->
    F (n, x) = (Int.floor ((n : ℝ) * f x) : ℝ) / (n : ℝ))
  (h5 : lpUniformConvergentOn F (Set.Icc a b) f)
  : lpUniformConvergentOn F (Set.Icc a b) f := by
  sorry
