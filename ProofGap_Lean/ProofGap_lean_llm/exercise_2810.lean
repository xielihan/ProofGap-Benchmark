import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2810
-- Exercise 2810, gaps *

def UniformConvergent2810 (f : ℕ × ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 -> ∃ N : ℕ, ∀ n : ℕ, n ≥ N -> ∀ x : ℝ, x ∈ S -> |f (n, x) - g x| < ε

noncomputable abbrev series2810 (a : ℕ -> ℝ) : ℝ := ∑' n, if 1 ≤ n then a n else 0
noncomputable abbrev part2810 (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.rpow x (1 /. (2 * k + 1)) - Real.rpow x (1 /. (2 * k - 1)))
noncomputable abbrev sumfun2810 (x : ℝ) : ℝ :=
  series2810 (fun n => Real.rpow x (1 /. (2 * n + 1)) - Real.rpow x (1 /. (2 * n - 1)))
noncomputable abbrev integral2810 (g : ℝ -> ℝ) : ℝ := ∫ x in (0 : ℝ)..(1 : ℝ), g x

theorem proof_gap_exercise_2810_1
  (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn : Prop)
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) -> Sn (n, 0) = 0 ∧ Sn (n, 1) = 0 := by
  sorry

theorem proof_gap_exercise_2810_2 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 : Prop)
  : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ ({m : ℕ | 0 < m}) ∧ x ∈ Set.Ioo (0 : ℝ) 1 ->
      Sn (n, x) = Real.rpow x (1 /. (2 * n + 1)) - x := by
  sorry

theorem proof_gap_exercise_2810_3 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 : Prop)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (0 : ℝ) 1 ->
      S x = if x = 0 ∨ x = 1 then 0 else 1 - x := by
  sorry

theorem proof_gap_exercise_2810_4 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4)
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ->
      ∃ x : ℕ -> ℝ, x n = (1 : ℝ) / ((2 : ℝ) ^ (2 * n + 1)) ∧ |Sn (n, x n) - S (x n)| = (1 /. 2) ∧ (1 /. 2) > epsilon0 := by
  sorry

theorem proof_gap_exercise_2810_5 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 : Prop) (epsilon0 : ℝ) (heps : epsilon0 = 1 /. 4)
  : ¬ UniformConvergent2810 Sn (Set.Icc (0 : ℝ) 1) S := by
  sorry

theorem proof_gap_exercise_2810_6 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 : Prop)
  : integral2810 (fun x => S x) = integral2810 (fun x => 1 - x) := by
  sorry

theorem proof_gap_exercise_2810_7 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 h6 : Prop)
  : integral2810 (fun x => 1 - x) = 1 /. 2 := by
  sorry

theorem proof_gap_exercise_2810_8 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 h6 h7 : Prop)
  : integral2810 (fun x => S x) = 1 /. 2 := by
  sorry

theorem proof_gap_exercise_2810_9 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 h6 h7 h8 : Prop)
  : series2810 (fun n => integral2810 (fun x => Real.rpow x (1 /. (2 * n + 1)) - Real.rpow x (1 /. (2 * n - 1)))) =
      series2810 (fun n => (2 * n + 1 : ℝ) /. (2 * n + 2) - (2 * n - 1 : ℝ) /. (2 * n)) := by
  sorry

theorem proof_gap_exercise_2810_10 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 h6 h7 h8 h9 : Prop)
  : series2810 (fun n => (2 * n + 1 : ℝ) /. (2 * n + 2) - (2 * n - 1 : ℝ) /. (2 * n)) =
      series2810 (fun n => 1 /. (2 * n) - 1 /. (2 * n + 2)) := by
  sorry

theorem proof_gap_exercise_2810_11 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : Prop)
  : series2810 (fun n => 1 /. (2 * n) - 1 /. (2 * n + 2)) = 1 /. 2 := by
  sorry

theorem proof_gap_exercise_2810_12 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 : Prop)
  : series2810 (fun n => integral2810 (fun x => Real.rpow x (1 /. (2 * n + 1)) - Real.rpow x (1 /. (2 * n - 1)))) = 1 /. 2 := by
  sorry

theorem proof_gap_exercise_2810_13 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 : Prop)
  : integral2810 (fun x => S x) =
      series2810 (fun n => integral2810 (fun x => Real.rpow x (1 /. (2 * n + 1)) - Real.rpow x (1 /. (2 * n - 1)))) := by
  sorry

theorem proof_gap_exercise_2810_14 (S : ℝ -> ℝ) (Sn : ℕ × ℝ -> ℝ) (hS hSn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 : Prop)
  : integral2810 (fun x => S x) =
      series2810 (fun n => integral2810 (fun x => Real.rpow x (1 /. (2 * n + 1)) - Real.rpow x (1 /. (2 * n - 1)))) := by
  sorry
