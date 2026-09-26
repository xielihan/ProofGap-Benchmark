import Mathlib

set_option linter.style.longLine false

open scoped Topology BigOperators
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def ex3782_f (a x : ℝ) : ℝ := Real.exp (-x) /. Real.rpow |Real.sin x| a
noncomputable def ex3782_piece (a : ℝ) (n : ℕ) : ℝ :=
  ∫ x in ((n : ℝ) * Real.pi)..(((n + 1 : ℕ) : ℝ) * Real.pi), ex3782_f a x
noncomputable def ex3782_shifted (a : ℝ) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi, Real.exp (-((n : ℝ) * Real.pi + t)) /. Real.rpow (Real.sin t) a
noncomputable def ex3782_major (a0 : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi, 1 /. Real.rpow (Real.sin t) a0
noncomputable def ex3782_improper (a A : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..A, ex3782_f a x
def ex3782_uniformImproperOn (F : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  TendstoUniformlyOn (fun A a => ex3782_improper a A) F atTop s
def ex3782_uniformSeriesOn (u : ℕ -> ℝ -> ℝ) (F : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  TendstoUniformlyOn (fun N a => ∑ n in Finset.range N, u n a) F atTop s

-- exercise: exercise_3782

theorem proof_gap_exercise_3782_1
    (F : ℝ -> ℝ) :
    ∀ a : ℝ, 0 < a -> a < 1 -> F a = ∑' n : ℕ, ex3782_piece a n := by
  sorry

theorem proof_gap_exercise_3782_2
    (F : ℝ -> ℝ) :
    ∀ a : ℝ, 0 < a -> a < 1 -> F a = ∑' n : ℕ, ex3782_shifted a n := by
  sorry

theorem proof_gap_exercise_3782_3
    (F : ℝ -> ℝ) :
    ∀ a0 : ℝ, 0 < a0 -> a0 < 1 ->
      ∀ n : ℕ, ∀ a : ℝ, 0 < a -> a ≤ a0 ->
        ex3782_shifted a n ≤ Real.exp (-((n : ℝ) * Real.pi)) * ex3782_major a0 := by
  sorry

theorem proof_gap_exercise_3782_4
    (F : ℝ -> ℝ) :
    ∀ a0 : ℝ, 0 < a0 -> a0 < 1 ->
      ex3782_major a0 = 2 * (∫ t in (0 : ℝ)..(Real.pi /. 2), 1 /. Real.rpow (Real.sin t) a0) := by
  sorry

theorem proof_gap_exercise_3782_5
    (F : ℝ -> ℝ) :
    ∀ a0 : ℝ, 0 < a0 -> a0 < 1 ->
      MeasureTheory.IntegrableOn (fun t => 1 /. Real.rpow (Real.sin t) a0) (Set.Ioo (0 : ℝ) Real.pi) := by
  sorry

theorem proof_gap_exercise_3782_6
    (F : ℝ -> ℝ) :
    ∀ a0 : ℝ, 0 < a0 -> a0 < 1 ->
      Summable (fun n : ℕ => Real.exp (-((n : ℝ) * Real.pi)) * ex3782_major a0) := by
  sorry

theorem proof_gap_exercise_3782_7
    (F : ℝ -> ℝ) :
    ∀ a0 : ℝ, 0 < a0 -> a0 < 1 ->
      ex3782_uniformSeriesOn (fun n a => ex3782_shifted a n) F (Set.Ioc (0 : ℝ) a0) := by
  sorry

theorem proof_gap_exercise_3782_8
    (F : ℝ -> ℝ) :
    ∀ a0 : ℝ, 0 < a0 -> a0 < 1 ->
      ex3782_uniformImproperOn F (Set.Ioc (0 : ℝ) a0) := by
  sorry

theorem proof_gap_exercise_3782_9
    (F : ℝ -> ℝ) :
    ∀ a0 : ℝ, 0 < a0 -> a0 < 1 -> ContinuousOn F (Set.Ioc (0 : ℝ) a0) := by
  sorry

theorem proof_gap_exercise_3782_10
    (F : ℝ -> ℝ) :
    ContinuousOn F (Set.Ioo (0 : ℝ) 1) := by
  sorry

theorem proof_gap_exercise_3782_11
    (F : ℝ -> ℝ)
    (hcont : ContinuousOn F (Set.Ioo (0 : ℝ) 1)) :
    ContinuousOn F (Set.Ioo (0 : ℝ) 1) := by
  sorry
