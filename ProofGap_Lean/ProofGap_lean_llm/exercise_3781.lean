import Mathlib

set_option linter.style.longLine false

open scoped Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def ex3781_f (a x : ℝ) : ℝ := Real.sin x /. (x ^ a * (Real.pi - x) ^ a)
noncomputable def ex3781_left (a : ℝ) : ℝ := ∫ x in (0 : ℝ)..(Real.pi /. 2), ex3781_f a x
noncomputable def ex3781_full (a : ℝ) : ℝ := ∫ x in (0 : ℝ)..Real.pi, ex3781_f a x
def ex3781_uniformImproperOn (G : ℝ -> ℝ) (s : Set ℝ) (F : ℝ -> ℝ) : Prop := ∀ a ∈ s, G a = F a

-- exercise: exercise_3781

theorem proof_gap_exercise_3781_1 (F : ℝ -> ℝ)
  (h1 : ∀ a, a ∈ Set.univ ∧ 0 < a ∧ a < 2 -> F a = ex3781_full a) :
  ∀ a, a ∈ Set.univ ∧ 0 < a ∧ a < 2 ->
    F a = ex3781_left a + (∫ x in (Real.pi /. 2)..Real.pi, ex3781_f a x) := by
  sorry

theorem proof_gap_exercise_3781_2 (F : ℝ -> ℝ) (h1 h2 : Prop) :
  ∀ a, a ∈ Set.univ ∧ 0 < a ∧ a < 2 ->
    (∫ x in (Real.pi /. 2)..Real.pi, ex3781_f a x) = ex3781_left a := by
  sorry

theorem proof_gap_exercise_3781_3 (F : ℝ -> ℝ) (h1 h2 h3 : Prop) :
  ∀ a, a ∈ Set.univ ∧ 0 < a ∧ a < 2 -> F a = 2 * ex3781_left a := by
  sorry

theorem proof_gap_exercise_3781_4 (F : ℝ -> ℝ) (h1 h2 h3 h4 : Prop) :
  ∀ a0, a0 ∈ Set.univ ∧ 0 < a0 -> ∀ a1, a1 ∈ Set.univ ∧ a0 ≤ a1 ∧ a1 < 2 ->
    ∀ eta, eta ∈ Set.univ ∧ 0 < eta ∧ eta < 1 -> ∀ a, a ∈ Set.univ ∧ a0 ≤ a ∧ a ≤ a1 ->
      (∫ x in (0 : ℝ)..eta, |Real.sin x| /. (x ^ a * (Real.pi - x) ^ a)) ≤
        (2 /. Real.pi) ^ a * (∫ x in (0 : ℝ)..eta, 1 /. x ^ (a - 1)) := by
  sorry

theorem proof_gap_exercise_3781_5 (F : ℝ -> ℝ) (h1 h2 h3 h4 h5 : Prop) :
  ∀ a0, a0 ∈ Set.univ ∧ 0 < a0 -> ∀ a1, a1 ∈ Set.univ ∧ a0 ≤ a1 ∧ a1 < 2 ->
    ∀ eta, eta ∈ Set.univ ∧ 0 < eta ∧ eta < 1 -> ∀ a, a ∈ Set.univ ∧ a0 ≤ a ∧ a ≤ a1 ->
      (2 /. Real.pi) ^ a * (∫ x in (0 : ℝ)..eta, 1 /. x ^ (a - 1)) ≤
        (2 /. Real.pi) ^ a0 * (∫ x in (0 : ℝ)..eta, 1 /. x ^ (a1 - 1)) := by
  sorry

theorem proof_gap_exercise_3781_6 (F : ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 : Prop) :
  ∀ a0, a0 ∈ Set.univ ∧ 0 < a0 -> ∀ a1, a1 ∈ Set.univ ∧ a0 ≤ a1 ∧ a1 < 2 ->
    ∀ eta, eta ∈ Set.univ ∧ 0 < eta ∧ eta < 1 -> ∀ a, a ∈ Set.univ ∧ a0 ≤ a ∧ a ≤ a1 ->
      (∫ x in (0 : ℝ)..eta, |Real.sin x| /. (x ^ a * (Real.pi - x) ^ a)) ≤
        (2 /. Real.pi) ^ a0 * (∫ x in (0 : ℝ)..eta, 1 /. x ^ (a1 - 1)) := by
  sorry

theorem proof_gap_exercise_3781_7 (F : ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 : Prop) :
  ∀ a0, a0 ∈ Set.univ ∧ 0 < a0 -> ∀ a1, a1 ∈ Set.univ ∧ a0 ≤ a1 ∧ a1 < 2 ->
    ∀ eta, eta ∈ Set.univ ∧ 0 < eta ∧ eta < 1 -> ∀ a, a ∈ Set.univ ∧ a0 ≤ a ∧ a ≤ a1 ->
      (2 /. Real.pi) ^ a0 * (∫ x in (0 : ℝ)..eta, 1 /. x ^ (a1 - 1)) =
        (2 /. Real.pi) ^ a0 * (eta ^ (2 - a1) /. (2 - a1)) := by
  sorry

theorem proof_gap_exercise_3781_8 (F : ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 : Prop) :
  ∀ a0, a0 ∈ Set.univ ∧ 0 < a0 -> ∀ a1, a1 ∈ Set.univ ∧ a0 ≤ a1 ∧ a1 < 2 ->
    ∀ eps, eps ∈ Set.univ ∧ eps > 0 ->
      ∃ delta, delta ∈ Set.univ ∧ delta = min 1 (((2 - a1) * (Real.pi /. 2) ^ a0 * eps) ^ (1 /. (2 - a1))) ∧
        ∀ eta, eta ∈ Set.univ ∧ 0 < eta ∧ eta < delta -> ∀ a, a ∈ Set.univ ∧ a0 ≤ a ∧ a ≤ a1 ->
          |(∫ x in (0 : ℝ)..eta, ex3781_f a x)| < eps := by
  sorry

theorem proof_gap_exercise_3781_9 (F : ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 : Prop) :
  ∀ a0, a0 ∈ Set.univ ∧ 0 < a0 -> ∀ a1, a1 ∈ Set.univ ∧ a0 ≤ a1 ∧ a1 < 2 ->
    ∀ a, a ∈ Set.univ ∧ a0 ≤ a ∧ a ≤ a1 -> ex3781_uniformImproperOn ex3781_left (Set.Icc a0 a1) F := by
  sorry

theorem proof_gap_exercise_3781_10 (F : ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : Prop) :
  ∀ a0, a0 ∈ Set.univ ∧ 0 < a0 -> ∀ a1, a1 ∈ Set.univ ∧ a0 ≤ a1 ∧ a1 < 2 ->
    ContinuousOn F (Set.Icc a0 a1) := by
  sorry

theorem proof_gap_exercise_3781_11 (F : ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : Prop)
  (h11 : ∀ a0, a0 ∈ Set.univ ∧ 0 < a0 -> ∀ a1, a1 ∈ Set.univ ∧ a0 ≤ a1 ∧ a1 < 2 -> ContinuousOn F (Set.Icc a0 a1)) :
  ContinuousOn F (Set.Ioo (0 : ℝ) 2) := by
  sorry

theorem proof_gap_exercise_3781_12 (F : ℝ -> ℝ) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 : Prop)
  (h12 : ContinuousOn F (Set.Ioo (0 : ℝ) 2)) :
  ContinuousOn F (Set.Ioo (0 : ℝ) 2) := by
  sorry
