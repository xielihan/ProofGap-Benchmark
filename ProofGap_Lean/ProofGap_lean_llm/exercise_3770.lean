import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

noncomputable abbrev properInt (a b : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in a..b, f x
def UniformConvergentParam (I : ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ α ∈ S, |I α - g α| < ε + δ

-- exercise: exercise_3770

theorem proof_gap_exercise_3770_1
  (I I1 I2 : ℝ -> ℝ)
  (hI : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    I α = properInt 0 1 (fun x => Real.sin (α * x) / Real.sqrt |x - α|))
  (hI1 : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    I1 α = properInt 0 α (fun x => Real.sin (α * x) / Real.sqrt (α - x)))
  (hI2 : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    I2 α = properInt α 1 (fun x => Real.sin (α * x) / Real.sqrt (x - α)))
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 -> I α = I1 α + I2 α := by
  sorry

theorem proof_gap_exercise_3770_2
  (I I1 I2 : ℝ -> ℝ) (hsplit : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 -> I α = I1 α + I2 α)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ η : ℝ, η ∈ (Set.univ : Set ℝ) ∧ η = ε ^ 2 / 8 ∧ 0 < η := by
  sorry

theorem proof_gap_exercise_3770_3
  (I I1 I2 : ℝ -> ℝ)
  (hηpos : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ η : ℝ, η ∈ (Set.univ : Set ℝ) ∧ η = ε ^ 2 / 8 ∧ 0 < η)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ η : ℝ, η ∈ (Set.univ : Set ℝ) ∧ η = ε ^ 2 / 8 ∧ η < ε ^ 2 / 4 := by
  sorry

theorem proof_gap_exercise_3770_4
  (I I1 I2 : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
    ∃ η : ℝ, η ∈ (Set.univ : Set ℝ) ∧ η = ε ^ 2 / 8 ∧
      (∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ∧ α - η ≥ 0 ->
        |properInt (α - η) α (fun x => Real.sin (α * x) / Real.sqrt (α - x))| ≤
          properInt (α - η) α (fun x => 1 / Real.sqrt (α - x)) ∧
        properInt (α - η) α (fun x => 1 / Real.sqrt (α - x)) = 2 * Real.sqrt η ∧
        2 * Real.sqrt η < ε) := by
  sorry

theorem proof_gap_exercise_3770_5
  (I I1 I2 : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
    ∃ η : ℝ, η ∈ (Set.univ : Set ℝ) ∧ η = ε ^ 2 / 8 ∧
      (∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ∧ α + η ≤ 1 ->
        |properInt α (α + η) (fun x => Real.sin (α * x) / Real.sqrt (x - α))| ≤
          properInt α (α + η) (fun x => 1 / Real.sqrt (x - α)) ∧
        properInt α (α + η) (fun x => 1 / Real.sqrt (x - α)) = 2 * Real.sqrt η ∧
        2 * Real.sqrt η < ε) := by
  sorry

theorem proof_gap_exercise_3770_6
  (I I1 I2 : ℝ -> ℝ)
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    UniformConvergentParam I1 (Set.Icc 0 1)
      (fun a => properInt 0 a (fun x => Real.sin (a * x) / Real.sqrt (a - x))) := by
  sorry

theorem proof_gap_exercise_3770_7
  (I I1 I2 : ℝ -> ℝ)
  (huc1 : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    UniformConvergentParam I1 (Set.Icc 0 1)
      (fun a => properInt 0 a (fun x => Real.sin (a * x) / Real.sqrt (a - x))))
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    UniformConvergentParam I2 (Set.Icc 0 1)
      (fun a => properInt a 1 (fun x => Real.sin (a * x) / Real.sqrt (x - a))) := by
  sorry

theorem proof_gap_exercise_3770_8
  (I I1 I2 : ℝ -> ℝ)
  (huc1 : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    UniformConvergentParam I1 (Set.Icc 0 1)
      (fun a => properInt 0 a (fun x => Real.sin (a * x) / Real.sqrt (a - x))))
  (huc2 : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    UniformConvergentParam I2 (Set.Icc 0 1)
      (fun a => properInt a 1 (fun x => Real.sin (a * x) / Real.sqrt (x - a))))
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    UniformConvergentParam I (Set.Icc 0 1)
      (fun a => properInt 0 1 (fun x => Real.sin (a * x) / Real.sqrt |x - a|)) := by
  sorry

theorem proof_gap_exercise_3770_9
  (I I1 I2 : ℝ -> ℝ)
  (hfinal : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    UniformConvergentParam I (Set.Icc 0 1)
      (fun a => properInt 0 1 (fun x => Real.sin (a * x) / Real.sqrt |x - a|)))
  : ∀ α : ℝ, α ∈ (Set.univ : Set ℝ) ∧ 0 ≤ α ∧ α ≤ 1 ->
    UniformConvergentParam I (Set.Icc 0 1)
      (fun a => properInt 0 1 (fun x => Real.sin (a * x) / Real.sqrt |x - a|)) := by
  sorry
