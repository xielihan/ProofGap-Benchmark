import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open MeasureTheory

noncomputable section

-- exercise: exercise_3951

def UnitDisk3951 : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

theorem proof_gap_exercise_3951_1
  (Ω : Set (ℝ × ℝ)) (f : ℝ -> ℝ)
  (hΩ : Ω = UnitDisk3951)
  (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
  : ∀ r, 0 ≤ r ∧ r ≤ 1 ->
      (∫ p in Ω, f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))) =
        ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ r in (0 : ℝ)..1, f r * r := by
  sorry

theorem proof_gap_exercise_3951_2
  (Ω : Set (ℝ × ℝ)) (f : ℝ -> ℝ)
  (hΩ : Ω = UnitDisk3951)
  (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
  (h6 : ∀ r, 0 ≤ r ∧ r ≤ 1 ->
      (∫ p in Ω, f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))) =
        ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ r in (0 : ℝ)..1, f r * r)
  : ∀ r, 0 ≤ r ∧ r ≤ 1 ->
      (∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ r in (0 : ℝ)..1, f r * r) =
        2 * Real.pi * (∫ r in (0 : ℝ)..1, r * f r) := by
  sorry

theorem proof_gap_exercise_3951_3
  (Ω : Set (ℝ × ℝ)) (f : ℝ -> ℝ)
  (hΩ : Ω = UnitDisk3951)
  (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
  (h6 : ∀ r, 0 ≤ r ∧ r ≤ 1 ->
      (∫ p in Ω, f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))) =
        ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ r in (0 : ℝ)..1, f r * r)
  (h7 : ∀ r, 0 ≤ r ∧ r ≤ 1 ->
      (∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ r in (0 : ℝ)..1, f r * r) =
        2 * Real.pi * (∫ r in (0 : ℝ)..1, r * f r))
  : ∀ r, 0 ≤ r ∧ r ≤ 1 ->
      (∫ p in Ω, f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))) =
        2 * Real.pi * (∫ r in (0 : ℝ)..1, r * f r) := by
  sorry

