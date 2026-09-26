import Mathlib

set_option linter.style.longLine false

open Filter MeasureTheory
open scoped Topology

noncomputable def iteratedDeriv : Nat -> (ℝ -> ℝ) -> ℝ -> ℝ
  | 0, f => f
  | n + 1, f => deriv (iteratedDeriv n f)

noncomputable abbrev DefInt (a b : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in a..b, f x
noncomputable abbrev FunDeri (f : ℝ -> ℝ) (_coord order : Nat) : ℝ -> ℝ := iteratedDeriv order f
def ContinuousFuncOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop := ContinuousOn f s
def IntegrableFuncOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop := IntegrableOn f s volume

-- Endpoint-improper integrals from the text are represented by interval integrals.
noncomputable def e3798I (alpha : ℝ) : ℝ :=
  DefInt 0 1 (fun x => Real.log (1 - alpha ^ 2 * x ^ 2) / Real.sqrt (1 - x ^ 2))

noncomputable def e3798J (alpha : ℝ) : ℝ :=
  DefInt 0 1 (fun x => 1 / ((1 - alpha ^ 2 * x ^ 2) * Real.sqrt (1 - x ^ 2)))

theorem proof_gap_exercise_3798_1 :
    ContinuousFuncOn e3798I (Set.Icc (-1) 1) := by sorry

theorem proof_gap_exercise_3798_2 :
    ∀ alpha0 : ℝ, 0 < alpha0 -> alpha0 < 1 ->
      ∀ alpha : ℝ, |alpha| ≤ alpha0 ->
        IntegrableFuncOn
          (fun x => FunDeri (fun a => Real.log (1 - a ^ 2 * x ^ 2) / Real.sqrt (1 - x ^ 2)) 1 1 alpha)
          (Set.Icc 0 1) := by sorry

theorem proof_gap_exercise_3798_3 (alpha : ℝ) :
    |alpha| < 1 ∧ alpha ≠ 0 ->
      FunDeri e3798I 1 1 alpha =
        DefInt 0 1 (fun x => (-2 * alpha * x ^ 2) / ((1 - alpha ^ 2 * x ^ 2) * Real.sqrt (1 - x ^ 2))) := by sorry

theorem proof_gap_exercise_3798_4 (alpha : ℝ) :
    |alpha| < 1 ∧ alpha ≠ 0 ->
      FunDeri e3798I 1 1 alpha =
        (2 / alpha) *
          DefInt 0 1 (fun x => (1 - alpha ^ 2 * x ^ 2 - 1) / ((1 - alpha ^ 2 * x ^ 2) * Real.sqrt (1 - x ^ 2))) := by sorry

theorem proof_gap_exercise_3798_5 (alpha : ℝ) :
    |alpha| < 1 ∧ alpha ≠ 0 ->
      FunDeri e3798I 1 1 alpha =
        (2 / alpha) * DefInt 0 1 (fun x => 1 / Real.sqrt (1 - x ^ 2)) -
          (2 / alpha) * e3798J alpha := by sorry

theorem proof_gap_exercise_3798_6 :
    DefInt 0 1 (fun x => 1 / Real.sqrt (1 - x ^ 2)) = Real.pi / 2 := by sorry

theorem proof_gap_exercise_3798_7 (alpha : ℝ) :
    |alpha| < 1 ->
      e3798J alpha = Real.pi / (2 * Real.sqrt (1 - alpha ^ 2)) := by sorry

theorem proof_gap_exercise_3798_8 (alpha : ℝ) :
    |alpha| < 1 ∧ alpha ≠ 0 ->
      FunDeri e3798I 1 1 alpha =
        Real.pi / alpha - Real.pi / (alpha * Real.sqrt (1 - alpha ^ 2)) := by sorry

theorem proof_gap_exercise_3798_9 :
    ∀ alpha : ℝ, |alpha| < 1 ∧ alpha ≠ 0 ->
      HasDerivAt e3798I
        (Real.pi / alpha - Real.pi / (alpha * Real.sqrt (1 - alpha ^ 2))) alpha := by sorry

theorem proof_gap_exercise_3798_10 (alpha : ℝ) :
    ∃ C : ℝ, |alpha| < 1 ∧ alpha ≠ 0 ->
      e3798I alpha =
        Real.pi * Real.log |alpha| +
          Real.pi * Real.log |(1 + Real.sqrt (1 - alpha ^ 2)) / alpha| + C := by sorry

theorem proof_gap_exercise_3798_11 (alpha : ℝ) :
    ∃ C : ℝ, |alpha| < 1 ∧ alpha ≠ 0 ->
      e3798I alpha = Real.pi * Real.log (1 + Real.sqrt (1 - alpha ^ 2)) + C := by sorry

theorem proof_gap_exercise_3798_12 :
    e3798I 0 = 0 := by sorry

theorem proof_gap_exercise_3798_13 :
    ∃ C : ℝ, 0 = Real.pi * Real.log 2 + C := by sorry

theorem proof_gap_exercise_3798_14 :
    ∃ C : ℝ, e3798I 0 = Real.pi * Real.log 2 + C := by sorry

theorem proof_gap_exercise_3798_15 :
    ∃ C : ℝ, C = -Real.pi * Real.log 2 := by sorry

theorem proof_gap_exercise_3798_16 (alpha : ℝ) :
    |alpha| < 1 ->
      e3798I alpha = Real.pi * Real.log ((1 + Real.sqrt (1 - alpha ^ 2)) / 2) := by sorry

theorem proof_gap_exercise_3798_17 :
    e3798I 1 = Real.pi * Real.log (1 / 2) := by sorry

theorem proof_gap_exercise_3798_18 :
    e3798I (-1) = Real.pi * Real.log (1 / 2) := by sorry

theorem proof_gap_exercise_3798_19 (alpha : ℝ) (halpha : |alpha| ≤ 1) :
    e3798I alpha = Real.pi * Real.log ((1 + Real.sqrt (1 - alpha ^ 2)) / 2) := by sorry
