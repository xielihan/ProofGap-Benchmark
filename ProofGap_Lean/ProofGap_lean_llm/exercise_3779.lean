import Mathlib

set_option linter.style.longLine false

open scoped Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def ex3779_integral (a : ℝ) : ℝ :=
  ∫ x in Set.Ici (0 : ℝ), x /. (2 + x ^ a)

def ex3779_uniformImproperOn (G : ℝ -> ℝ) (s : Set ℝ) (F : ℝ -> ℝ) : Prop :=
  ∀ a ∈ s, G a = F a

-- exercise: exercise_3779

theorem proof_gap_exercise_3779_1
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a) :
  ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 ->
    ∀ x : ℝ, x ∈ Set.univ ->
      ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < x /. (2 + x ^ a) := by
  sorry

theorem proof_gap_exercise_3779_2
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 ->
    ∀ x : ℝ, x ∈ Set.univ ->
      ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < x /. (2 + x ^ a)) :
  ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 ->
    ∀ x : ℝ, x ∈ Set.univ ->
        ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. (2 + x ^ a)) < (x /. x ^ a) := by
  sorry

theorem proof_gap_exercise_3779_3
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < x /. (2 + x ^ a))
    (h3 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. (2 + x ^ a)) < (x /. x ^ a)) :
  ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 ->
    ∀ x : ℝ, x ∈ Set.univ ->
        ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. x ^ a) ≤ (1 /. x ^ (a0 - 1)) := by
  sorry

theorem proof_gap_exercise_3779_4
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < x /. (2 + x ^ a))
    (h3 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. (2 + x ^ a)) < (x /. x ^ a))
    (h4 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. x ^ a) ≤ (1 /. x ^ (a0 - 1))) :
  ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 ->
    ∀ x : ℝ, x ∈ Set.univ ->
      ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < 1 /. x ^ (a0 - 1) := by
  sorry

theorem proof_gap_exercise_3779_5
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < x /. (2 + x ^ a))
    (h3 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. (2 + x ^ a)) < (x /. x ^ a))
    (h4 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. x ^ a) ≤ (1 /. x ^ (a0 - 1)))
  (h5 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < 1 /. x ^ (a0 - 1)) :
  ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 ->
      (((∫ x in Set.Ici (1 : ℝ), 1 /. x ^ (a0 - 1)) : ℝ) : EReal) < ⊤ := by
  sorry

theorem proof_gap_exercise_3779_6
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < x /. (2 + x ^ a))
    (h3 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. (2 + x ^ a)) < (x /. x ^ a))
    (h4 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> (x /. x ^ a) ≤ (1 /. x ^ (a0 - 1)))
  (h5 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ∀ x : ℝ, x ∈ Set.univ -> ∀ a : ℝ, a ∈ Set.univ ∧ x ≥ 1 ∧ a ≥ a0 -> 0 < 1 /. x ^ (a0 - 1))
    (h6 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> (((∫ x in Set.Ici (1 : ℝ), 1 /. x ^ (a0 - 1)) : ℝ) : EReal) < ⊤) :
  ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 ->
    ex3779_uniformImproperOn (fun a => ∫ x in Set.Ici (1 : ℝ), x /. (2 + x ^ a)) (Set.Ici a0) F := by
  sorry

theorem proof_gap_exercise_3779_7
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 h3 h4 h5 h6 : Prop)
  (h7 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ex3779_uniformImproperOn (fun a => ∫ x in Set.Ici (1 : ℝ), x /. (2 + x ^ a)) (Set.Ici a0) F) :
  ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 ->
    ContinuousOn (fun p : ℝ × ℝ => p.1 /. (2 + p.1 ^ p.2)) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ici a0) := by
  sorry

theorem proof_gap_exercise_3779_8
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 h3 h4 h5 h6 : Prop)
  (h7 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ex3779_uniformImproperOn (fun a => ∫ x in Set.Ici (1 : ℝ), x /. (2 + x ^ a)) (Set.Ici a0) F)
  (h8 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ContinuousOn (fun p : ℝ × ℝ => p.1 /. (2 + p.1 ^ p.2)) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ici a0)) :
  ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ContinuousOn F (Set.Ici a0) := by
  sorry

theorem proof_gap_exercise_3779_9
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 h3 h4 h5 h6 h7 h8 : Prop)
  (h9 : ∀ a0 : ℝ, a0 ∈ Set.univ ∧ a0 > 2 -> ContinuousOn F (Set.Ici a0)) :
  ContinuousOn F (Set.Ioi (2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3779_10
  (F : ℝ -> ℝ)
  (h1 : ∀ a : ℝ, a ∈ Set.univ ∧ a > 2 -> F a = ex3779_integral a)
  (h2 h3 h4 h5 h6 h7 h8 h9 : Prop)
  (h10 : ContinuousOn F (Set.Ioi (2 : ℝ))) :
  ContinuousOn F (Set.Ioi (2 : ℝ)) := by
  sorry
