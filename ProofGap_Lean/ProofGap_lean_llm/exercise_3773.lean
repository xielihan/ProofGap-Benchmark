import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

noncomputable abbrev improperInt (a : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in Set.Ioi a, f x
def ConvergentImproper (a : ℝ) (f : ℝ -> ℝ) : Prop :=
  MeasureTheory.HasFiniteIntegral f (MeasureTheory.volume.restrict (Set.Ioi a))
def IntegrableFuncOn (f : ℝ -> ℝ) (S : Set ℝ) : Prop :=
  MeasureTheory.IntegrableOn f S

-- exercise: exercise_3773

theorem proof_gap_exercise_3773_1
  (f : ℝ -> ℝ)
  (hf : IntegrableFuncOn f (Set.Ioi 0))
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ α ∈ Set.Icc 0 1 ->
      ConvergentImproper 0 (fun x => Real.exp (-(α * x)) * f x) := by
  sorry

theorem proof_gap_exercise_3773_2
  (f : ℝ -> ℝ)
  (hf : IntegrableFuncOn f (Set.Ioi 0))
  (hconv : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ α ∈ Set.Icc 0 1 -> ConvergentImproper 0 (fun x => Real.exp (-(α * x)) * f x))
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ η A0 : ℝ, η ∈ (Set.univ : Set ℝ) ∧ A0 ∈ (Set.univ : Set ℝ) ∧ η > 0 ∧ A0 > 0 ∧ η < A0 ∧
        (∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ α ∈ Set.Icc 0 1 ->
          |∫ x in 0..η, Real.exp (-(α * x)) * f x| < ε / 5 ∧
          |improperInt A0 (fun x => Real.exp (-(α * x)) * f x)| < ε / 5) := by
  sorry

theorem proof_gap_exercise_3773_3
  (f : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ η A0 M0 : ℝ, η ∈ (Set.univ : Set ℝ) ∧ A0 ∈ (Set.univ : Set ℝ) ∧ M0 ∈ (Set.univ : Set ℝ) ∧
        η > 0 ∧ A0 > 0 ∧ η < A0 ∧ M0 > 0 ∧
        (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ η ≤ x ∧ x ≤ A0 -> |f x| ≤ M0) := by
  sorry

theorem proof_gap_exercise_3773_4
  (f : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ η A0 M0 δ : ℝ, η ∈ (Set.univ : Set ℝ) ∧ A0 ∈ (Set.univ : Set ℝ) ∧ M0 ∈ (Set.univ : Set ℝ) ∧ δ ∈ (Set.univ : Set ℝ) ∧
        η > 0 ∧ A0 > 0 ∧ η < A0 ∧ M0 > 0 ∧ δ > 0 ∧ δ < 1 ∧
        (∀ α x : ℝ, α ∈ (Set.univ : Set ℝ) ∧ x ∈ (Set.univ : Set ℝ) ∧ 0 < α ∧ α < δ ∧ η ≤ x ∧ x ≤ A0 ->
          0 ≤ 1 - Real.exp (-(α * x)) ∧ 1 - Real.exp (-(α * x)) < ε / (5 * A0 * M0)) := by
  sorry

theorem proof_gap_exercise_3773_5
  (f : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ η A0 δ : ℝ, η ∈ (Set.univ : Set ℝ) ∧ A0 ∈ (Set.univ : Set ℝ) ∧ δ ∈ (Set.univ : Set ℝ) ∧
        η > 0 ∧ A0 > 0 ∧ η < A0 ∧ δ > 0 ∧
        (∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 < α ∧ α < δ ->
          |improperInt 0 (fun x => Real.exp (-(α * x)) * f x) - improperInt 0 f| =
          |(∫ x in η..A0, (Real.exp (-(α * x)) - 1) * f x) +
            improperInt A0 (fun x => Real.exp (-(α * x)) * f x) - improperInt A0 f +
            (∫ x in 0..η, Real.exp (-(α * x)) * f x) - (∫ x in 0..η, f x)|) := by
  sorry

theorem proof_gap_exercise_3773_6
  (f : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ A0 M0 δ : ℝ, A0 ∈ (Set.univ : Set ℝ) ∧ M0 ∈ (Set.univ : Set ℝ) ∧ δ ∈ (Set.univ : Set ℝ) ∧
        A0 > 0 ∧ M0 > 0 ∧ δ > 0 ∧
        (∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 < α ∧ α < δ ->
          |improperInt 0 (fun x => Real.exp (-(α * x)) * f x) - improperInt 0 f| <
            M0 * A0 * (ε / (5 * A0 * M0)) + ε / 5 + ε / 5 + ε / 5 + ε / 5) := by
  sorry

theorem proof_gap_exercise_3773_7
  (f : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
        (∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 < α ∧ α < δ ->
          |improperInt 0 (fun x => Real.exp (-(α * x)) * f x) - improperInt 0 f| < ε) := by
  sorry

theorem proof_gap_exercise_3773_8
  (f : ℝ -> ℝ)
  (hlim : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
        (∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 < α ∧ α < δ ->
          |improperInt 0 (fun x => Real.exp (-(α * x)) * f x) - improperInt 0 f| < ε))
  : Tendsto (fun α : ℝ => improperInt 0 (fun x => Real.exp (-(α * x)) * f x)) (𝓝[>] 0) (𝓝 (improperInt 0 f)) := by
  sorry

theorem proof_gap_exercise_3773_9
  (f : ℝ -> ℝ)
  (hfinal : Tendsto (fun α : ℝ => improperInt 0 (fun x => Real.exp (-(α * x)) * f x)) (𝓝[>] 0) (𝓝 (improperInt 0 f)))
  : Tendsto (fun α : ℝ => improperInt 0 (fun x => Real.exp (-(α * x)) * f x)) (𝓝[>] 0) (𝓝 (improperInt 0 f)) := by
  sorry
