import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2804
-- Exercise 2804, gaps *

def UniformConvergent2804 (f : ℕ × ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 -> ∃ N : ℕ, ∀ n : ℕ, n ≥ N -> ∀ x : ℝ, x ∈ S -> |f (n, x) - g x| < ε

noncomputable abbrev seqLim2804 (u : ℕ -> ℝ) : ℝ := limUnder atTop u
noncomputable abbrev integral2804 (g : ℝ -> ℝ) : ℝ := ∫ x in (0 : ℝ)..(1 : ℝ), g x
noncomputable abbrev testSeq2804 : ℕ -> ℝ := fun n => 1 /. (n + 1)
noncomputable abbrev eps2804 : ℝ := 1 /. (3 * Real.exp 1)

theorem proof_gap_exercise_2804_1
  (f : ℕ × ℝ -> ℝ)
  (hf : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Icc (0 : ℝ) 1 ->
    f (n, x) = (n : ℝ) * x * (1 - x) ^ n)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) ->
      ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) -> f (n, x) = 0 := by
  sorry

theorem proof_gap_exercise_2804_2 (f : ℕ × ℝ -> ℝ)
  (hf : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Icc (0 : ℝ) 1 -> f (n, x) = (n : ℝ) * x * (1 - x) ^ n)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) -> f (n, x) = 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2804_3 (f : ℕ × ℝ -> ℝ) (hf : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Icc (0 : ℝ) 1 -> f (n, x) = (n : ℝ) * x * (1 - x) ^ n)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) -> f (n, x) = 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> seqLim2804 (fun n => f (n, x)) = seqLim2804 (fun n => (n : ℝ) * x * (1 - x) ^ n) := by
  sorry

theorem proof_gap_exercise_2804_4 (f : ℕ × ℝ -> ℝ) (hf : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Icc (0 : ℝ) 1 -> f (n, x) = (n : ℝ) * x * (1 - x) ^ n)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) -> f (n, x) = 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> seqLim2804 (fun n => f (n, x)) = seqLim2804 (fun n => (n : ℝ) * x * (1 - x) ^ n))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> Tendsto (fun n : ℕ => (n : ℝ) * x * (1 - x) ^ n) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2804_5 (f : ℕ × ℝ -> ℝ) (hf : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Icc (0 : ℝ) 1 -> f (n, x) = (n : ℝ) * x * (1 - x) ^ n)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) -> f (n, x) = 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> seqLim2804 (fun n => f (n, x)) = seqLim2804 (fun n => (n : ℝ) * x * (1 - x) ^ n))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> Tendsto (fun n : ℕ => (n : ℝ) * x * (1 - x) ^ n) atTop (𝓝 0))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2804_6 (f : ℕ × ℝ -> ℝ) (hf : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Icc (0 : ℝ) 1 -> f (n, x) = (n : ℝ) * x * (1 - x) ^ n)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) -> f (n, x) = 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = 0 ∨ x = 1) -> Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> seqLim2804 (fun n => f (n, x)) = seqLim2804 (fun n => (n : ℝ) * x * (1 - x) ^ n))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> Tendsto (fun n : ℕ => (n : ℝ) * x * (1 - x) ^ n) atTop (𝓝 0))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 -> Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (0 : ℝ) 1 -> Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2804_7 (f : ℕ × ℝ -> ℝ) (hf : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Icc (0 : ℝ) 1 -> f (n, x) = (n : ℝ) * x * (1 - x) ^ n)
  (h1 h2 h3 h4 h5 h6 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = eps2804)
  : ∃ x : (ℕ -> ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x n = 1 /. (n + 1)) -> x n ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

theorem proof_gap_exercise_2804_8 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = eps2804)
  : ∃ x : (ℕ -> ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x n = 1 /. (n + 1)) -> |f (n, x n) - 0| = (n : ℝ) * (1 /. (n + 1)) * (1 - (1 /. (n + 1))) ^ n := by
  sorry

theorem proof_gap_exercise_2804_9 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = eps2804)
  : ∃ x : (ℕ -> ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x n = 1 /. (n + 1)) -> (n : ℝ) * (1 /. (n + 1)) * (1 - (1 /. (n + 1))) ^ n = ((n : ℝ) /. (n + 1)) ^ (n + 1) := by
  sorry

theorem proof_gap_exercise_2804_10 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = eps2804)
  : ∃ x : (ℕ -> ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x n = 1 /. (n + 1)) -> |f (n, x n) - 0| = ((n : ℝ) /. (n + 1)) ^ (n + 1) := by
  sorry

theorem proof_gap_exercise_2804_11 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = eps2804)
  : ∃ x : (ℕ -> ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x n = 1 /. (n + 1)) -> Tendsto (fun n : ℕ => ((n : ℝ) /. (n + 1)) ^ (n + 1)) atTop (𝓝 ((Real.exp 1)⁻¹)) := by
  sorry

theorem proof_gap_exercise_2804_12 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = eps2804)
  : ∃ x : (ℕ -> ℝ), ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x n = 1 /. (n + 1)) -> ∃ n0 : ℕ, n0 ∈ (Set.univ : Set ℕ) ∧ n0 ∈ ({m : ℕ | 0 < m}) ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ n > n0 -> |f (n, x n)| > (1 /. (2 * Real.exp 1)) ∧ (1 /. (2 * Real.exp 1)) > epsilon0 := by
  sorry

theorem proof_gap_exercise_2804_13 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = eps2804)
  : ¬ UniformConvergent2804 f (Set.Icc (0 : ℝ) 1) (fun _ => 0) := by
  sorry

theorem proof_gap_exercise_2804_14 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 : Prop)
  : integral2804 (fun x => seqLim2804 (fun n => f (n, x))) = integral2804 (fun _ => 0) := by
  sorry

theorem proof_gap_exercise_2804_15 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 : Prop)
  : integral2804 (fun _ => 0) = 0 := by
  sorry

theorem proof_gap_exercise_2804_16 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 : Prop)
  : integral2804 (fun x => seqLim2804 (fun n => f (n, x))) = 0 := by
  sorry

theorem proof_gap_exercise_2804_17 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 : Prop)
  : Tendsto (fun n : ℕ => integral2804 (fun x => f (n, x))) atTop (𝓝 (seqLim2804 (fun n => integral2804 (fun x => (n : ℝ) * x * (1 - x) ^ n)))) := by
  sorry

theorem proof_gap_exercise_2804_18 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 : Prop)
  : seqLim2804 (fun n => integral2804 (fun x => (n : ℝ) * x * (1 - x) ^ n)) = seqLim2804 (fun n => (n : ℝ) /. ((n + 1) * (n + 2))) := by
  sorry

theorem proof_gap_exercise_2804_19 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 : Prop)
  : Tendsto (fun n : ℕ => (n : ℝ) /. ((n + 1) * (n + 2))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2804_20 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 : Prop)
  : Tendsto (fun n : ℕ => integral2804 (fun x => f (n, x))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2804_21 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 : Prop)
  : seqLim2804 (fun n => integral2804 (fun x => f (n, x))) = integral2804 (fun x => seqLim2804 (fun n => f (n, x))) := by
  sorry

theorem proof_gap_exercise_2804_22 (f : ℕ × ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 : Prop)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (0 : ℝ) 1 ->
      Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 0) ∧
      ¬ UniformConvergent2804 f (Set.Icc (0 : ℝ) 1) (fun _ => 0) ∧
      seqLim2804 (fun n => integral2804 (fun x => f (n, x))) = integral2804 (fun x => seqLim2804 (fun n => f (n, x))) := by
  sorry
