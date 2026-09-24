import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable abbrev improperInt (a b : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in a..b, f x
def UniformConvergentParam (I : ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ α ∈ S, |I α - g α| < ε + δ

-- exercise: exercise_3769

theorem proof_gap_exercise_3769_1
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  : I 1 = infinity := by
  sorry

theorem proof_gap_exercise_3769_2
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (h1 : I 1 = infinity)
  : I 2 = infinity := by
  sorry

theorem proof_gap_exercise_3769_3
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (h1 : I 1 = infinity) (h2 : I 2 = infinity)
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) =
      improperInt 0 1 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) +
      improperInt 1 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) := by
  sorry

theorem proof_gap_exercise_3769_4
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (h1 : I 1 = infinity) (h2 : I 2 = infinity)
  (hsplit : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) =
      improperInt 0 1 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) +
      improperInt 1 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  : ∀ x α : ℝ, x ∈ (Set.univ : Set ℝ) ∧ α ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 ∧ |α| < (1 /. 2) ->
    |Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)| <
      1 / (Real.rpow x (1 /. 2) * Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3)) := by
  sorry

theorem proof_gap_exercise_3769_5
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (h1 : I 1 = infinity) (h2 : I 2 = infinity)
  (hsplit : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) =
      improperInt 0 1 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) +
      improperInt 1 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (hbound0 : ∀ x α : ℝ, x ∈ (Set.univ : Set ℝ) ∧ α ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 ∧ |α| < (1 /. 2) ->
    |Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)| <
      1 / (Real.rpow x (1 /. 2) * Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3)))
  : ∀ x α : ℝ, x ∈ (Set.univ : Set ℝ) ∧ α ∈ (Set.univ : Set ℝ) ∧ 1 < x ∧ x < 2 ∧ |α| < (1 /. 2) ->
    |Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)| <
      Real.sqrt 2 / (Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3)) := by
  sorry

theorem proof_gap_exercise_3769_6
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (h1 : I 1 = infinity) (h2 : I 2 = infinity)
  (hsplit : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) =
      improperInt 0 1 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)) +
      improperInt 1 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (hbound0 : ∀ x α : ℝ, x ∈ (Set.univ : Set ℝ) ∧ α ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < 1 ∧ |α| < (1 /. 2) ->
    |Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)| <
      1 / (Real.rpow x (1 /. 2) * Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3)))
  (hbound1 : ∀ x α : ℝ, x ∈ (Set.univ : Set ℝ) ∧ α ∈ (Set.univ : Set ℝ) ∧ 1 < x ∧ x < 2 ∧ |α| < (1 /. 2) ->
    |Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)| <
      Real.sqrt 2 / (Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3)))
  : improperInt 0 1 (fun x => 1 / (Real.rpow x (1 /. 2) * Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3))) < infinity := by
  sorry

theorem proof_gap_exercise_3769_7
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (h1 : I 1 = infinity) (h2 : I 2 = infinity)
  (hconv0 : improperInt 0 1 (fun x => 1 / (Real.rpow x (1 /. 2) * Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3))) < infinity)
  : improperInt 1 2 (fun x => Real.sqrt 2 / (Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3))) < infinity := by
  sorry

theorem proof_gap_exercise_3769_8
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (hconv0 : improperInt 0 1 (fun x => 1 / (Real.rpow x (1 /. 2) * Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3))) < infinity)
  (hconv1 : improperInt 1 2 (fun x => Real.sqrt 2 / (Real.rpow (1 - x) (1 /. 3) * Real.rpow (x - 2) (2 /. 3))) < infinity)
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    UniformConvergentParam I (Set.Ioo (-(1 /. 2)) (1 /. 2))
      (fun a => improperInt 0 2 (fun x => Real.rpow x a / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3))) := by
  sorry

theorem proof_gap_exercise_3769_9
  (I : ℝ -> ℝ) (infinity : ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    I α = improperInt 0 2 (fun x => Real.rpow x α / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3)))
  (hfinal : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    UniformConvergentParam I (Set.Ioo (-(1 /. 2)) (1 /. 2))
      (fun a => improperInt 0 2 (fun x => Real.rpow x a / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3))))
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ |α| < (1 /. 2) ->
    UniformConvergentParam I (Set.Ioo (-(1 /. 2)) (1 /. 2))
      (fun a => improperInt 0 2 (fun x => Real.rpow x a / Real.rpow ((x - 1) * (x - 2) ^ 2) (1 /. 3))) := by
  sorry
