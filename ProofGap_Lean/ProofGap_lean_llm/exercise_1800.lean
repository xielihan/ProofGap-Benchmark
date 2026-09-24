import Mathlib

/-!
exercise_1800, gaps 1-4.
The DSL's `RealSet` is represented by `ℝ`.
-/

namespace Exercise1800

abbrev FSet (p : (ℝ → ℝ) → Prop) : Set (ℝ → ℝ) := {F | p F}
noncomputable abbrev D (F : ℝ → ℝ) (x : ℝ) : ℝ := deriv F x
noncomputable abbrev Did (x : ℝ) : ℝ := deriv (fun y : ℝ => y) x
abbrev SetValueAt (S : Set (ℝ → ℝ)) (x value : ℝ) : Prop := ∃ F ∈ S, F x = value

theorem proof_gap_exercise_1800_1 :
    FSet (fun F2 => ∀ x : ℝ, D F2 x = x * Real.sinh x * Did x)
      =
    FSet (fun F3 => ∀ x : ℝ, D F3 x = x * D (fun y : ℝ => Real.cosh y) x) := by
  sorry

theorem proof_gap_exercise_1800_2
    (h1 :
      FSet (fun F2 => ∀ x : ℝ, D F2 x = x * Real.sinh x * Did x)
        =
      FSet (fun F3 => ∀ x : ℝ, D F3 x = x * D (fun y : ℝ => Real.cosh y) x)) :
    FSet (fun F4 => ∀ x : ℝ, D F4 x = x * D (fun y : ℝ => Real.cosh y) x)
      =
    FSet (fun F7 => ∃ F5 : ℝ → ℝ,
      (∀ x : ℝ, D F5 x = Real.cosh x * Did x ∧ F7 x = x * Real.cosh x - F5 x)) := by
  sorry

theorem proof_gap_exercise_1800_3
    (h1 :
      FSet (fun F2 => ∀ x : ℝ, D F2 x = x * Real.sinh x * Did x)
        =
      FSet (fun F3 => ∀ x : ℝ, D F3 x = x * D (fun y : ℝ => Real.cosh y) x))
    (h2 :
      FSet (fun F4 => ∀ x : ℝ, D F4 x = x * D (fun y : ℝ => Real.cosh y) x)
        =
      FSet (fun F7 => ∃ F5 : ℝ → ℝ,
        (∀ x : ℝ, D F5 x = Real.cosh x * Did x ∧ F7 x = x * Real.cosh x - F5 x))) :
    ∀ x : ℝ,
      SetValueAt
        (FSet (fun F8 => ∀ y : ℝ, D F8 y = Real.cosh y * Did y))
        x (Real.sinh x) := by
  sorry

theorem proof_gap_exercise_1800_4
    (h1 :
      FSet (fun F2 => ∀ x : ℝ, D F2 x = x * Real.sinh x * Did x)
        =
      FSet (fun F3 => ∀ x : ℝ, D F3 x = x * D (fun y : ℝ => Real.cosh y) x))
    (h2 :
      FSet (fun F4 => ∀ x : ℝ, D F4 x = x * D (fun y : ℝ => Real.cosh y) x)
        =
      FSet (fun F7 => ∃ F5 : ℝ → ℝ,
        (∀ x : ℝ, D F5 x = Real.cosh x * Did x ∧ F7 x = x * Real.cosh x - F5 x)))
    (h3 :
      ∀ x : ℝ,
        SetValueAt
          (FSet (fun F8 => ∀ y : ℝ, D F8 y = Real.cosh y * Did y))
          x (Real.sinh x)) :
    FSet (fun F9 => ∀ x : ℝ, D F9 x = x * Real.sinh x * Did x)
      =
    FSet (fun F10 => ∃ C : ℝ, ∀ x : ℝ,
      F10 x = x * Real.cosh x - Real.sinh x + C) := by
  sorry

end Exercise1800
