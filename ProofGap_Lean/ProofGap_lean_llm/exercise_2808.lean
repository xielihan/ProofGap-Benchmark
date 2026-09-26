import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def UniformConvergent2808 (f : ℕ × ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 -> ∃ N : ℕ, ∀ n : ℕ, n ≥ N -> ∀ x : ℝ, x ∈ S -> |f (n, x) - g x| < ε

def MonoDecFuncOn2808 (f : ℝ -> ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≤ y -> f x ≥ f y

noncomputable abbrev rightLim2808 (u : ℝ -> ℝ) : ℝ := limUnder (𝓝[>] (0 : ℝ)) u
noncomputable abbrev series2808 (a : ℕ -> ℝ) : ℝ := ∑' n, if 1 ≤ n then a n else 0
noncomputable abbrev term2808 (n : ℕ) (x : ℝ) : ℝ := 1 /. ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x)

abbrev ex2808_g1 : Prop :=
  ∀ l : ℝ, l > 0 ->
    ∀ n : ℕ, 0 < n ->
      MonoDecFuncOn2808 (fun x => 1 /. Real.rpow (n : ℝ) x) (Set.Icc 0 l) ∧
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) l -> (1 /. Real.rpow (n : ℝ) x) ≤ 1
abbrev ex2808_g2 : Prop :=
  ∀ l : ℝ, l > 0 -> UniformConvergent2808 (fun p => 1 /. (2 : ℝ) ^ p.1) (Set.Icc 0 l) (fun _ => 1)
abbrev ex2808_g3 : Prop :=
  ∀ l : ℝ, l > 0 ->
    UniformConvergent2808 (fun p => term2808 p.1 p.2) (Set.Icc 0 l)
      (fun x => series2808 (fun n => term2808 n x))
abbrev ex2808_g4 : Prop :=
  ∀ l : ℝ, l > 0 -> ∀ n : ℕ, 0 < n -> ContinuousOn (fun x : ℝ => term2808 n x) (Set.Icc 0 l)
abbrev ex2808_g5 : Prop :=
  ∀ n : ℕ, 0 < n -> Tendsto (fun x : ℝ => term2808 n x) (𝓝[>] (0 : ℝ)) (𝓝 (1 /. (2 : ℝ) ^ n))
abbrev ex2808_g6 : Prop :=
  Tendsto (fun x : ℝ => series2808 (fun n => term2808 n x)) (𝓝[>] (0 : ℝ))
    (𝓝 (series2808 (fun n => rightLim2808 (fun x => term2808 n x))))
abbrev ex2808_g7 : Prop :=
  series2808 (fun n => rightLim2808 (fun x => term2808 n x)) = series2808 (fun n => 1 /. (2 : ℝ) ^ n)
abbrev ex2808_g8 : Prop := series2808 (fun n => 1 /. (2 : ℝ) ^ n) = 1
abbrev ex2808_g9 : Prop :=
  Tendsto (fun x : ℝ => series2808 (fun n => term2808 n x)) (𝓝[>] (0 : ℝ)) (𝓝 1)

theorem proof_gap_exercise_2808_1 : ex2808_g1 := by
  sorry

theorem proof_gap_exercise_2808_2 (h1 : ex2808_g1) : ex2808_g2 := by
  sorry

theorem proof_gap_exercise_2808_3 (h1 : ex2808_g1) (h2 : ex2808_g2) : ex2808_g3 := by
  sorry

theorem proof_gap_exercise_2808_4 (h1 : ex2808_g1) (h2 : ex2808_g2) (h3 : ex2808_g3) : ex2808_g4 := by
  sorry

theorem proof_gap_exercise_2808_5 (h1 : ex2808_g1) (h2 : ex2808_g2) (h3 : ex2808_g3) (h4 : ex2808_g4) : ex2808_g5 := by
  sorry

theorem proof_gap_exercise_2808_6 (h1 : ex2808_g1) (h2 : ex2808_g2) (h3 : ex2808_g3) (h4 : ex2808_g4) (h5 : ex2808_g5) : ex2808_g6 := by
  sorry

theorem proof_gap_exercise_2808_7 (h1 : ex2808_g1) (h2 : ex2808_g2) (h3 : ex2808_g3) (h4 : ex2808_g4) (h5 : ex2808_g5) (h6 : ex2808_g6) : ex2808_g7 := by
  sorry

theorem proof_gap_exercise_2808_8 (h1 : ex2808_g1) (h2 : ex2808_g2) (h3 : ex2808_g3) (h4 : ex2808_g4) (h5 : ex2808_g5) (h6 : ex2808_g6) (h7 : ex2808_g7) : ex2808_g8 := by
  sorry

theorem proof_gap_exercise_2808_9 (h1 : ex2808_g1) (h2 : ex2808_g2) (h3 : ex2808_g3) (h4 : ex2808_g4) (h5 : ex2808_g5) (h6 : ex2808_g6) (h7 : ex2808_g7) (h8 : ex2808_g8) : ex2808_g9 := by
  sorry
