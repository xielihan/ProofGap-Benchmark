import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open scoped Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def tailIntegral (f : ℝ -> ℝ -> ℝ) (b y : ℝ) : ℝ :=
  ∫ x in Set.Ioi b, f x y

noncomputable def partialIntegral (f : ℝ -> ℝ -> ℝ) (b y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..b, f x y

def uniformlyConvergesImproperIntegral
    (f : ℝ -> ℝ -> ℝ) (s : Set ℝ) (F : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun b y => partialIntegral f b y) F atTop s

-- exercise: exercise_3751

-- Gap 1: the stated tail condition is restated as itself for every positive epsilon_0.
theorem proof_gap_exercise_3751_1
    (f : ℝ -> ℝ -> ℝ) (y1 y2 : ℝ)
    (hy : y1 < y2)
    (hf_dom : ∀ y ∈ Set.Ioo y1 y2, MeasureTheory.IntegrableOn (fun x => f x y) (Set.Ici (0 : ℝ))) :
    (∀ ε0 : ℝ,
      ε0 ∈ Set.Ioi (0 : ℝ) ->
      (∀ B : ℝ, B > 0 ->
        ∃ b0 : ℝ, ∃ y0 : ℝ,
          b0 ≥ B ∧ y0 ∈ Set.Ioo y1 y2 ∧ ε0 ≤ |tailIntegral f b0 y0|) ->
      (∀ B : ℝ, B > 0 ->
        ∃ b0 : ℝ, ∃ y0 : ℝ,
          b0 ≥ B ∧ y0 ∈ Set.Ioo y1 y2 ∧ ε0 ≤ |tailIntegral f b0 y0|)) := by
  sorry

-- Gap 2: the positive lower-tail obstruction implies non-uniform convergence on (y1,y2).
theorem proof_gap_exercise_3751_2
    (f : ℝ -> ℝ -> ℝ) (y1 y2 : ℝ)
    (hy : y1 < y2)
    (h_tail :
      ∃ ε0 : ℝ, ε0 > 0 ∧
        ∀ B : ℝ, B > 0 ->
          ∃ b0 : ℝ, ∃ y0 : ℝ,
            b0 ≥ B ∧ y0 ∈ Set.Ioo y1 y2 ∧ ε0 ≤ |tailIntegral f b0 y0|) :
    ¬ uniformlyConvergesImproperIntegral f (Set.Ioo y1 y2)
        (fun y => ∫ x in Set.Ioi (0 : ℝ), f x y) := by
  sorry

-- Gap 3: final formulation of non-uniform convergence criterion.
theorem proof_gap_exercise_3751_3
    (f : ℝ -> ℝ -> ℝ) (y1 y2 : ℝ)
    (hy : y1 < y2)
    (h_tail :
      ∃ ε0 : ℝ, ε0 > 0 ∧
        ∀ B : ℝ, B > 0 ->
          ∃ b0 : ℝ, ∃ y0 : ℝ,
            b0 ≥ B ∧ y0 ∈ Set.Ioo y1 y2 ∧ ε0 ≤ |tailIntegral f b0 y0|) :
    ¬ uniformlyConvergesImproperIntegral f (Set.Ioo y1 y2)
        (fun y => ∫ x in Set.Ioi (0 : ℝ), f x y) := by
  sorry
