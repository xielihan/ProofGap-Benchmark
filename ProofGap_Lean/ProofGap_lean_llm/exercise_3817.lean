import Mathlib

set_option linter.style.longLine false

open Filter MeasureTheory
open scoped Topology

noncomputable def iteratedDeriv : Nat -> (ℝ -> ℝ) -> ℝ -> ℝ
  | 0, f => f
  | n + 1, f => deriv (iteratedDeriv n f)

noncomputable abbrev IntInf (a : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in Set.Ioi a, f x ∂volume
noncomputable abbrev DefInt (a b : ℝ) (f : ℝ -> ℝ) : ℝ := intervalIntegral.integral a b f
noncomputable abbrev FunDeri (f : ℝ -> ℝ) (_coord order : Nat) : ℝ -> ℝ := iteratedDeriv order f
def UniformConvergentOn (F : Nat -> ℝ -> ℝ) (S : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn F g atTop S
def ContinuousFuncOn (f : ℝ -> ℝ) (S : Set ℝ) : Prop := ContinuousOn f S
def IntegrableAtInfinity (f : ℝ -> ℝ) (a : ℝ) : Prop := IntegrableOn f (Set.Ioi a) volume

noncomputable def e3817I (alpha : ℝ) : ℝ :=
  IntInf 0 (fun x => (Real.sin (alpha * x) / x) ^ 2)

theorem proof_gap_exercise_3817_1 (alpha : ℝ) (halpha : 0 ≤ alpha) :
    Tendsto (fun x : ℝ => (Real.sin (alpha * x) / x) ^ 2) (𝓝[>] 0) (𝓝 (alpha ^ 2)) := by sorry

theorem proof_gap_exercise_3817_2 (alpha : ℝ) (halpha : 0 ≤ alpha) :
    ∀ x : ℝ, 0 < x -> (Real.sin (alpha * x) / x) ^ 2 ≤ 1 / x ^ 2 := by sorry

theorem proof_gap_exercise_3817_3 (alpha : ℝ) (halpha : 0 ≤ alpha) :
    IntegrableAtInfinity (fun x => 1 / x ^ 2) 1 := by sorry

theorem proof_gap_exercise_3817_4 (R : ℝ) (hR : 0 < R) :
    UniformConvergentOn
      (fun n alpha => ∫ x in Set.Ioc 1 (n : ℝ), (Real.sin (alpha * x) / x) ^ 2 ∂volume)
      (Set.Icc 0 R)
      (fun alpha => IntInf 1 (fun x => (Real.sin (alpha * x) / x) ^ 2)) := by sorry

theorem proof_gap_exercise_3817_5 (R : ℝ) (hR : 0 < R) :
    UniformConvergentOn
      (fun n alpha => ∫ x in Set.Ioc 0 (n : ℝ), (Real.sin (alpha * x) / x) ^ 2 ∂volume)
      (Set.Icc 0 R) e3817I := by sorry

theorem proof_gap_exercise_3817_6 :
    ContinuousFuncOn e3817I (Set.Ici 0) := by sorry

theorem proof_gap_exercise_3817_7 (alpha : ℝ) :
    alpha > 0 ->
      IntInf 0 (fun x => FunDeri (fun a => (Real.sin (a * x) / x) ^ 2) 1 1 alpha) =
        IntInf 0 (fun x => Real.sin (2 * alpha * x) / x) := by sorry

theorem proof_gap_exercise_3817_8 (alpha : ℝ) :
    alpha > 0 -> IntInf 0 (fun x => Real.sin (2 * alpha * x) / x) = Real.pi / 2 := by sorry

theorem proof_gap_exercise_3817_9 (alpha : ℝ) :
    alpha > 0 ->
      FunDeri e3817I 1 1 alpha = IntInf 0 (fun x => Real.sin (2 * alpha * x) / x) := by sorry

theorem proof_gap_exercise_3817_10 (alpha : ℝ) :
    alpha > 0 -> IntInf 0 (fun x => Real.sin (2 * alpha * x) / x) = Real.pi / 2 := by sorry

theorem proof_gap_exercise_3817_11 (alpha : ℝ) :
    alpha > 0 -> FunDeri e3817I 1 1 alpha = Real.pi / 2 := by sorry

theorem proof_gap_exercise_3817_12 (alpha : ℝ) :
    ∃ C : ℝ, e3817I alpha = (Real.pi / 2) * alpha + C := by sorry

theorem proof_gap_exercise_3817_13 :
    e3817I 0 = 0 := by sorry

theorem proof_gap_exercise_3817_14 :
    ∃ C : ℝ, Tendsto e3817I (𝓝[>] 0) (𝓝 C) := by sorry

theorem proof_gap_exercise_3817_15 :
    ∃ C : ℝ, C = 0 := by sorry

theorem proof_gap_exercise_3817_16 (alpha : ℝ) (halpha : 0 ≤ alpha) :
    e3817I alpha = (Real.pi / 2) * alpha := by sorry

theorem proof_gap_exercise_3817_17 (alpha : ℝ) :
    alpha < 0 -> e3817I alpha = e3817I (-alpha) := by sorry

theorem proof_gap_exercise_3817_18 (alpha : ℝ) :
    alpha < 0 -> e3817I (-alpha) = (Real.pi / 2) * (-alpha) := by sorry

theorem proof_gap_exercise_3817_19 (alpha : ℝ) :
    e3817I alpha = (Real.pi / 2) * |alpha| := by sorry

theorem proof_gap_exercise_3817_20 (alpha : ℝ) :
    IntInf 0 (fun x => (Real.sin (alpha * x) / x) ^ 2) = (Real.pi / 2) * |alpha| := by sorry
