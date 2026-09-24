import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2808
-- Exercise 2808, gaps *

def UniformConvergent2808 (f : ℕ × ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 -> ∃ N : ℕ, ∀ n : ℕ, n ≥ N -> ∀ x : ℝ, x ∈ S -> |f (n, x) - g x| < ε

def MonoDecFuncOn2808 (f : ℝ -> ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≤ y -> f x ≥ f y

noncomputable abbrev rightLim2808 (u : ℝ -> ℝ) : ℝ := (𝓝[>] (0 : ℝ)).limUnder u
noncomputable abbrev series2808 (a : ℕ -> ℝ) : ℝ := ∑' n, if 1 ≤ n then a n else 0

theorem proof_gap_exercise_2808_1
  : ∀ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ l > 0 ->
      ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ->
        MonoDecFuncOn2808 (fun x => 1 /. Real.rpow (n : ℝ) x) (Set.Icc 0 l) ∧
        ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc 0 l -> (1 /. Real.rpow (n : ℝ) x) ≤ 1 := by
  sorry

theorem proof_gap_exercise_2808_2 (h1 : Prop)
  : ∀ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ l > 0 ->
      UniformConvergent2808 (fun p => 1 /. (2 : ℝ) ^ p.1) (Set.Icc 0 l) (fun _ => 1) := by
  sorry

theorem proof_gap_exercise_2808_3 (h1 h2 : Prop)
  : ∀ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ l > 0 ->
      UniformConvergent2808
        (fun p => 1 /. ((2 : ℝ) ^ p.1 * Real.rpow (p.1 : ℝ) p.2))
        (Set.Icc 0 l)
        (fun x => series2808 (fun n => 1 /. ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x))) := by
  sorry

theorem proof_gap_exercise_2808_4 (h1 h2 h3 : Prop)
  : ∀ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ l > 0 ->
      ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ->
        ContinuousOn (fun x : ℝ => 1 /. ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x)) (Set.Icc 0 l) := by
  sorry

theorem proof_gap_exercise_2808_5 (h1 h2 h3 h4 : Prop)
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ ({m : ℕ | 0 < m}) ->
      Tendsto (fun x : ℝ => 1 /. ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x)) (𝓝[>] (0 : ℝ)) (𝓝 (1 /. (2 : ℝ) ^ n)) := by
  sorry

theorem proof_gap_exercise_2808_6 (h1 h2 h3 h4 h5 : Prop)
  : Tendsto (fun x : ℝ => series2808 (fun n => 1 /. ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x))) (𝓝[>] (0 : ℝ))
      (𝓝 (series2808 (fun n => rightLim2808 (fun x => 1 /. ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x))))) := by
  sorry

theorem proof_gap_exercise_2808_7 (h1 h2 h3 h4 h5 h6 : Prop)
  : series2808 (fun n => rightLim2808 (fun x => 1 /. ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x))) =
      series2808 (fun n => 1 /. (2 : ℝ) ^ n) := by
  sorry

theorem proof_gap_exercise_2808_8 (h1 h2 h3 h4 h5 h6 h7 : Prop)
  : series2808 (fun n => 1 /. (2 : ℝ) ^ n) = 1 := by
  sorry

theorem proof_gap_exercise_2808_9 (h1 h2 h3 h4 h5 h6 h7 h8 : Prop)
  : Tendsto (fun x : ℝ => series2808 (fun n => 1 /. ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  sorry
