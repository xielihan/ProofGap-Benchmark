import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def UniformConvergent2805 (f : ℕ × ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 -> ∃ N : ℕ, ∀ n : ℕ, n ≥ N -> ∀ x : ℝ, x ∈ S -> |f (n, x) - g x| < ε

noncomputable abbrev seqLim2805 (u : ℕ -> ℝ) : ℝ := limUnder atTop u
noncomputable abbrev integral2805 (g : ℝ -> ℝ) : ℝ := ∫ x in (0 : ℝ)..(1 : ℝ), g x
noncomputable abbrev f2805 : ℕ × ℝ -> ℝ := fun p => (p.1 : ℝ) * p.2 /. (1 + (p.1 : ℝ) ^ 2 * p.2 ^ 4)
noncomputable abbrev pointwiseLim2805 (x : ℝ) : ℝ := limUnder atTop (fun n : ℕ => (n : ℝ) * x /. (1 + (n : ℝ) ^ 2 * x ^ 4))
noncomputable abbrev antideriv2805 (n : ℕ) (x : ℝ) : ℝ := (1 /. 2) * Real.arctan ((n : ℝ) * x ^ 2)

abbrev ex2805_g1 : Prop := integral2805 pointwiseLim2805 = integral2805 (fun _ => 0)
abbrev ex2805_g2 : Prop := integral2805 (fun _ => 0) = 0
abbrev ex2805_g3 : Prop := integral2805 pointwiseLim2805 = 0
abbrev ex2805_g4 : Prop :=
  seqLim2805 (fun n => integral2805 (fun x => (n : ℝ) * x /. (1 + (n : ℝ) ^ 2 * x ^ 4))) =
    seqLim2805 (fun n => antideriv2805 n 1 - antideriv2805 n 0)
abbrev ex2805_g5 : Prop := seqLim2805 (fun n => antideriv2805 n 1 - antideriv2805 n 0) = Real.pi /. 4
abbrev ex2805_g6 : Prop := seqLim2805 (fun n => integral2805 (fun x => (n : ℝ) * x /. (1 + (n : ℝ) ^ 2 * x ^ 4))) = Real.pi /. 4
abbrev ex2805_g7 : Prop :=
  integral2805 pointwiseLim2805 ≠ seqLim2805 (fun n => integral2805 (fun x => (n : ℝ) * x /. (1 + (n : ℝ) ^ 2 * x ^ 4)))
abbrev ex2805_g8 (f : ℕ × ℝ -> ℝ) : Prop :=
  ∀ x : ℝ, ∀ n : ℕ, 0 < n -> x = (1 /. (n : ℝ)) ->
    |f (n, x) - 0| = (((n : ℝ) * (1 /. (n : ℝ))) /. (1 + (n : ℝ) ^ 2 * (1 /. ((n : ℝ) ^ 4))))
abbrev ex2805_g9 : Prop :=
  ∀ x : ℝ, ∀ n : ℕ, 0 < n -> x = (1 /. (n : ℝ)) ->
    (((n : ℝ) * (1 /. (n : ℝ))) /. (1 + (n : ℝ) ^ 2 * (1 /. ((n : ℝ) ^ 4)))) > (1 /. 2)
abbrev ex2805_g10 (epsilon0 : ℝ) : Prop := ∀ x : ℝ, ∀ n : ℕ, 0 < n -> x = (1 /. (n : ℝ)) -> (1 /. 2) > epsilon0
abbrev ex2805_g11 (f : ℕ × ℝ -> ℝ) (epsilon0 : ℝ) : Prop :=
  ∀ x : ℝ, ∀ n : ℕ, 0 < n -> x = (1 /. (n : ℝ)) -> |f (n, x) - 0| > epsilon0
abbrev ex2805_g12 (f : ℕ × ℝ -> ℝ) : Prop := ¬ UniformConvergent2805 f (Set.Icc (0 : ℝ) 1) (fun _ => 0)

theorem proof_gap_exercise_2805_1 : ex2805_g1 := by
  sorry

theorem proof_gap_exercise_2805_2 (h1 : ex2805_g1) : ex2805_g2 := by
  sorry

theorem proof_gap_exercise_2805_3 (h1 : ex2805_g1) (h2 : ex2805_g2) : ex2805_g3 := by
  sorry

theorem proof_gap_exercise_2805_4 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) : ex2805_g4 := by
  sorry

theorem proof_gap_exercise_2805_5 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) : ex2805_g5 := by
  sorry

theorem proof_gap_exercise_2805_6 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) (h5 : ex2805_g5) : ex2805_g6 := by
  sorry

theorem proof_gap_exercise_2805_7 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) (h5 : ex2805_g5) (h6 : ex2805_g6) : ex2805_g7 := by
  sorry

theorem proof_gap_exercise_2805_8 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) (h5 : ex2805_g5) (h6 : ex2805_g6) (h7 : ex2805_g7)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3) : ex2805_g8 f := by
  sorry

theorem proof_gap_exercise_2805_9 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) (h5 : ex2805_g5) (h6 : ex2805_g6) (h7 : ex2805_g7)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3) (h8 : ex2805_g8 f) : ex2805_g9 := by
  sorry

theorem proof_gap_exercise_2805_10 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) (h5 : ex2805_g5) (h6 : ex2805_g6) (h7 : ex2805_g7)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3) (h8 : ex2805_g8 f) (h9 : ex2805_g9) : ex2805_g10 epsilon0 := by
  sorry

theorem proof_gap_exercise_2805_11 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) (h5 : ex2805_g5) (h6 : ex2805_g6) (h7 : ex2805_g7)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3) (h8 : ex2805_g8 f) (h9 : ex2805_g9) (h10 : ex2805_g10 epsilon0) : ex2805_g11 f epsilon0 := by
  sorry

theorem proof_gap_exercise_2805_12 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) (h5 : ex2805_g5) (h6 : ex2805_g6) (h7 : ex2805_g7)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3) (h8 : ex2805_g8 f) (h9 : ex2805_g9) (h10 : ex2805_g10 epsilon0) (h11 : ex2805_g11 f epsilon0) : ex2805_g12 f := by
  sorry

theorem proof_gap_exercise_2805_13 (h1 : ex2805_g1) (h2 : ex2805_g2) (h3 : ex2805_g3) (h4 : ex2805_g4) (h5 : ex2805_g5) (h6 : ex2805_g6) (h7 : ex2805_g7)
  (f : ℕ × ℝ -> ℝ) (hf : f = f2805) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 3) (h8 : ex2805_g8 f) (h9 : ex2805_g9) (h10 : ex2805_g10 epsilon0) (h11 : ex2805_g11 f epsilon0) (h12 : ex2805_g12 f) : ex2805_g6 := by
  sorry
