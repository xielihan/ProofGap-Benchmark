import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def UniformConvergent2810 (f : ℕ × ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 -> ∃ N : ℕ, ∀ n : ℕ, n ≥ N -> ∀ x : ℝ, x ∈ S -> |f (n, x) - g x| < ε

noncomputable abbrev series2810 (a : ℕ -> ℝ) : ℝ := ∑' n, if 1 ≤ n then a n else 0
noncomputable abbrev term2810 (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 /. (2 * n + 1)) - Real.rpow x (1 /. (2 * n - 1))
noncomputable abbrev part2810 (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) n, term2810 k x
noncomputable abbrev sumfun2810 (x : ℝ) : ℝ := series2810 (fun n => term2810 n x)
noncomputable abbrev integral2810 (g : ℝ -> ℝ) : ℝ := ∫ x in (0 : ℝ)..(1 : ℝ), g x

abbrev ex2810_Sdef (S : ℝ -> ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 -> S x = sumfun2810 x
abbrev ex2810_Sndef (Sn : ℕ × ℝ -> ℝ) : Prop :=
  ∀ n : ℕ, 0 < n -> ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 -> Sn (n, x) = part2810 n x
abbrev ex2810_g1 (Sn : ℕ × ℝ -> ℝ) : Prop :=
  ∀ n : ℕ, 0 < n -> Sn (n, 0) = 0 ∧ Sn (n, 1) = 0
abbrev ex2810_g2 (Sn : ℕ × ℝ -> ℝ) : Prop :=
  ∀ n : ℕ, ∀ x : ℝ, 0 < n -> x ∈ Set.Ioo (0 : ℝ) 1 -> Sn (n, x) = Real.rpow x (1 /. (2 * n + 1)) - x
abbrev ex2810_g3 (S : ℝ -> ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 -> S x = if x = 0 ∨ x = 1 then 0 else 1 - x
abbrev ex2810_g4 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (epsilon0 : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n ->
    ∃ x : ℕ -> ℝ, x n = (1 : ℝ) / ((2 : ℝ) ^ (2 * n + 1)) ∧
      |Sn (n, x n) - S (x n)| = (1 /. 2) ∧ (1 /. 2) > epsilon0
abbrev ex2810_g5 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) : Prop :=
  ¬ UniformConvergent2810 Sn (Set.Icc (0 : ℝ) 1) S
abbrev ex2810_g6 (S : ℝ -> ℝ) : Prop := integral2810 (fun x => S x) = integral2810 (fun x => 1 - x)
abbrev ex2810_g7 : Prop := integral2810 (fun x => 1 - x) = 1 /. 2
abbrev ex2810_g8 (S : ℝ -> ℝ) : Prop := integral2810 (fun x => S x) = 1 /. 2
abbrev ex2810_g9 : Prop :=
  series2810 (fun n => integral2810 (fun x => term2810 n x)) =
    series2810 (fun n => (2 * n + 1 : ℝ) /. (2 * n + 2) - (2 * n - 1 : ℝ) /. (2 * n))
abbrev ex2810_g10 : Prop :=
  series2810 (fun n => (2 * n + 1 : ℝ) /. (2 * n + 2) - (2 * n - 1 : ℝ) /. (2 * n)) =
    series2810 (fun n => 1 /. (2 * n) - 1 /. (2 * n + 2))
abbrev ex2810_g11 : Prop := series2810 (fun n => 1 /. (2 * n) - 1 /. (2 * n + 2)) = 1 /. 2
abbrev ex2810_g12 : Prop := series2810 (fun n => integral2810 (fun x => term2810 n x)) = 1 /. 2
abbrev ex2810_g13 (S : ℝ -> ℝ) : Prop :=
  integral2810 (fun x => S x) = series2810 (fun n => integral2810 (fun x => term2810 n x))

theorem proof_gap_exercise_2810_1
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) : ex2810_g1 Sn := by
  sorry

theorem proof_gap_exercise_2810_2
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) : ex2810_g2 Sn := by
  sorry

theorem proof_gap_exercise_2810_3
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) : ex2810_g3 S := by
  sorry

theorem proof_gap_exercise_2810_4
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) : ex2810_g4 S Sn epsilon0 := by
  sorry

theorem proof_gap_exercise_2810_5
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) : ex2810_g5 S Sn := by
  sorry

theorem proof_gap_exercise_2810_6
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) : ex2810_g6 S := by
  sorry

theorem proof_gap_exercise_2810_7
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) (h6 : ex2810_g6 S) : ex2810_g7 := by
  sorry

theorem proof_gap_exercise_2810_8
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) (h6 : ex2810_g6 S) (h7 : ex2810_g7) : ex2810_g8 S := by
  sorry

theorem proof_gap_exercise_2810_9
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) (h6 : ex2810_g6 S) (h7 : ex2810_g7) (h8 : ex2810_g8 S) : ex2810_g9 := by
  sorry

theorem proof_gap_exercise_2810_10
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) (h6 : ex2810_g6 S) (h7 : ex2810_g7) (h8 : ex2810_g8 S) (h9 : ex2810_g9) : ex2810_g10 := by
  sorry

theorem proof_gap_exercise_2810_11
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) (h6 : ex2810_g6 S) (h7 : ex2810_g7) (h8 : ex2810_g8 S) (h9 : ex2810_g9) (h10 : ex2810_g10) : ex2810_g11 := by
  sorry

theorem proof_gap_exercise_2810_12
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) (h6 : ex2810_g6 S) (h7 : ex2810_g7) (h8 : ex2810_g8 S) (h9 : ex2810_g9) (h10 : ex2810_g10) (h11 : ex2810_g11) : ex2810_g12 := by
  sorry

theorem proof_gap_exercise_2810_13
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) (h6 : ex2810_g6 S) (h7 : ex2810_g7) (h8 : ex2810_g8 S) (h9 : ex2810_g9) (h10 : ex2810_g10) (h11 : ex2810_g11) (h12 : ex2810_g12) : ex2810_g13 S := by
  sorry

theorem proof_gap_exercise_2810_14
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS : ex2810_Sdef S) (hSn : ex2810_Sndef Sn) (h1 : ex2810_g1 Sn) (h2 : ex2810_g2 Sn) (h3 : ex2810_g3 S)
  (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4) (h4 : ex2810_g4 S Sn epsilon0) (h5 : ex2810_g5 S Sn) (h6 : ex2810_g6 S) (h7 : ex2810_g7) (h8 : ex2810_g8 S) (h9 : ex2810_g9) (h10 : ex2810_g10) (h11 : ex2810_g11) (h12 : ex2810_g12) (h13 : ex2810_g13 S) : ex2810_g13 S := by
  sorry
