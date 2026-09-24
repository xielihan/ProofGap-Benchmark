import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2805
-- Exercise 2805, gaps *

def UniformConvergent2805 (f : ℕ × ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 -> ∃ N : ℕ, ∀ n : ℕ, n ≥ N -> ∀ x : ℝ, x ∈ S -> |f (n, x) - g x| < ε

noncomputable abbrev seqLim2805 (u : ℕ -> ℝ) : ℝ := limUnder atTop u
noncomputable abbrev rightLim2805 (u : ℝ -> ℝ) : ℝ := limUnder (𝓝[>] (0 : ℝ)) u
noncomputable abbrev integral2805 (g : ℝ -> ℝ) : ℝ := ∫ x in (0 : ℝ)..(1 : ℝ), g x
noncomputable abbrev f2805 : ℕ × ℝ -> ℝ := fun p => (p.1 : ℝ) * p.2 /. (1 + (p.1 : ℝ) ^ 2 * p.2 ^ 4)

theorem proof_gap_exercise_2805_1
  : integral2805 (fun x => rightLim2805 (fun n => (n * x) /. (1 + n ^ 2 * x ^ 4))) = integral2805 (fun _ => 0) := by
  sorry

theorem proof_gap_exercise_2805_2
  (h1 : integral2805 (fun x => rightLim2805 (fun n => (n * x) /. (1 + n ^ 2 * x ^ 4))) = integral2805 (fun _ => 0))
  : integral2805 (fun _ => 0) = 0 := by
  sorry

theorem proof_gap_exercise_2805_3
  (h1 : integral2805 (fun x => rightLim2805 (fun n => (n * x) /. (1 + n ^ 2 * x ^ 4))) = integral2805 (fun _ => 0))
  (h2 : integral2805 (fun _ => 0) = 0)
  : integral2805 (fun x => rightLim2805 (fun n => (n * x) /. (1 + n ^ 2 * x ^ 4))) = 0 := by
  sorry

theorem proof_gap_exercise_2805_4 (h1 h2 h3 : Prop)
  : seqLim2805 (fun n => integral2805 (fun x => (n : ℝ) * x /. (1 + (n : ℝ) ^ 2 * x ^ 4))) =
    seqLim2805 (fun n => ((fun x : ℝ => (1 /. 2) * Real.arctan ((n : ℝ) * x ^ 2)) 1 - (fun x : ℝ => (1 /. 2) * Real.arctan ((n : ℝ) * x ^ 2)) 0)) := by
  sorry

theorem proof_gap_exercise_2805_5 (h1 h2 h3 h4 : Prop)
  : seqLim2805 (fun n => ((fun x : ℝ => (1 /. 2) * Real.arctan ((n : ℝ) * x ^ 2)) 1 - (fun x : ℝ => (1 /. 2) * Real.arctan ((n : ℝ) * x ^ 2)) 0)) = Real.pi /. 4 := by
  sorry

theorem proof_gap_exercise_2805_6 (h1 h2 h3 h4 h5 : Prop)
  : seqLim2805 (fun n => integral2805 (fun x => (n : ℝ) * x /. (1 + (n : ℝ) ^ 2 * x ^ 4))) = Real.pi /. 4 := by
  sorry

theorem proof_gap_exercise_2805_7 (h1 h2 h3 h4 h5 h6 : Prop)
  : integral2805 (fun x => rightLim2805 (fun n => (n * x) /. (1 + n ^ 2 * x ^ 4))) ≠
    seqLim2805 (fun n => integral2805 (fun x => (n : ℝ) * x /. (1 + (n : ℝ) ^ 2 * x ^ 4))) := by
  sorry

theorem proof_gap_exercise_2805_8 (h1 h2 h3 h4 h5 h6 h7 : Prop)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x = 1 /. n) ->
      |f (n, x) - 0| = ((n : ℝ) * (1 /. n)) /. (1 + (n : ℝ) ^ 2 * (1 /. (n ^ 4))) := by
  sorry

theorem proof_gap_exercise_2805_9 (h1 h2 h3 h4 h5 h6 h7 h8 : Prop)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x = 1 /. n) ->
      (((n : ℝ) * (1 /. n)) / (1 + (n : ℝ) ^ 2 * (1 /. (n ^ 4)))) > (1 /. 2) := by
  sorry

theorem proof_gap_exercise_2805_10 (h1 h2 h3 h4 h5 h6 h7 h8 h9 : Prop)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x = 1 /. n) -> (1 /. 2) > epsilon0 := by
  sorry

theorem proof_gap_exercise_2805_11 (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : Prop)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ (x = 1 /. n) -> |f (n, x) - 0| > epsilon0 := by
  sorry

theorem proof_gap_exercise_2805_12 (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 : Prop)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3)
  : ¬ UniformConvergent2805 f (Set.Icc (0 : ℝ) 1) (fun _ => 0) := by
  sorry

theorem proof_gap_exercise_2805_13 (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 : Prop)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3)
  : seqLim2805 (fun n => integral2805 (fun x => (n : ℝ) * x /. (1 + (n : ℝ) ^ 2 * x ^ 4))) = Real.pi /. 4 := by
  sorry
