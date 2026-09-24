import Mathlib

set_option linter.style.longLine false

open scoped Topology
open Filter

noncomputable abbrev strip4163 : Set (ℝ × ℝ) := {q | q.2 ∈ Set.Icc (0 : ℝ) 1}
noncomputable abbrev F4163 (phi : ℝ -> ℝ -> ℝ) (p : ℝ) : ℝ × ℝ -> ℝ :=
  fun q => phi q.1 q.2 / ((1 + q.1 ^ (2 : ℕ) + q.2 ^ (2 : ℕ)) ^ p)
noncomputable abbrev G4163 (p : ℝ) : ℝ × ℝ -> ℝ :=
  fun q => 1 / ((1 + q.1 ^ (2 : ℕ) + q.2 ^ (2 : ℕ)) ^ p)
noncomputable abbrev H4163 (a p : ℝ) : ℝ -> ℝ := fun x => 1 / ((a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ p)

-- exercise: exercise_4163

theorem proof_gap_exercise_4163_1 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ)
  (hdef : ∀ y ∈ Set.Icc (0 : ℝ) 1, Continuous fun x => phi x y) (hbd : ∃ C, ∀ x y, y ∈ Set.Icc (0 : ℝ) 1 -> |phi x y| ≤ C) :
  I < ⊤ ↔ J < ⊤ := by
  sorry

theorem proof_gap_exercise_4163_2 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ)
  (hJ : J = (↑(∫ q in strip4163, G4163 p q) : WithTop ℝ)) : J = (↑(∫ q in strip4163, G4163 p q) : WithTop ℝ) := by
  sorry

theorem proof_gap_exercise_4163_3 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  (∫ q in strip4163, G4163 p q) = 2 * ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) := by
  sorry

theorem proof_gap_exercise_4163_4 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ)
  (hJ : J = (↑(∫ q in strip4163, G4163 p q) : WithTop ℝ)) :
  J = (↑(2 * ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) : ℝ) : WithTop ℝ) := by
  sorry

theorem proof_gap_exercise_4163_5 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 -> p ≥ 0 -> ∫ x in (0 : ℝ)..x, 1 / ((2 + x ^ (2 : ℕ)) ^ p) ≤ ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) := by
  sorry

theorem proof_gap_exercise_4163_6 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 -> p ≥ 0 -> ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) ≤ ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ)) ^ p) := by
  sorry

theorem proof_gap_exercise_4163_7 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  p ≥ 0 -> ∫ x in (0 : ℝ)..x, 1 / ((2 + x ^ (2 : ℕ)) ^ p) ≤ ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ)) ^ p) := by
  sorry

theorem proof_gap_exercise_4163_8 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  p ≥ 0 -> 2 * (∫ x in (0 : ℝ)..x, 1 / ((2 + x ^ (2 : ℕ)) ^ p)) ≤ J := by
  sorry

theorem proof_gap_exercise_4163_9 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  p ≥ 0 -> J ≤ 2 * (∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ)) ^ p)) := by
  sorry

theorem proof_gap_exercise_4163_10 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  p ≥ 0 -> 2 * (∫ x in (0 : ℝ)..x, 1 / ((2 + x ^ (2 : ℕ)) ^ p)) ≤ 2 * (∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ)) ^ p)) := by
  sorry

theorem proof_gap_exercise_4163_11 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 -> p < 0 -> ∫ x in (0 : ℝ)..x, 1 / ((2 + x ^ (2 : ℕ)) ^ p) ≥ ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) := by
  sorry

theorem proof_gap_exercise_4163_12 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 -> p < 0 -> ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) ≥ ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ)) ^ p) := by
  sorry

theorem proof_gap_exercise_4163_13 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  p < 0 -> ∫ x in (0 : ℝ)..x, 1 / ((2 + x ^ (2 : ℕ)) ^ p) ≥ ∫ x in (0 : ℝ)..x, 1 / ((1 + x ^ (2 : ℕ)) ^ p) := by
  sorry

theorem proof_gap_exercise_4163_14 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  ∀ a : ℝ, a > 0 -> Tendsto (fun x : ℝ => (x ^ (2 : ℕ)) ^ p * (1 / ((a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ p))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_4163_15 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  ∀ a : ℝ, a > 0 -> p > (1 / 2 : ℝ) -> MeasureTheory.IntegrableOn (H4163 a p) (Set.Ici 0) volume := by
  sorry

theorem proof_gap_exercise_4163_16 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  ∀ a : ℝ, a > 0 -> p < (1 / 2 : ℝ) -> ¬ MeasureTheory.IntegrableOn (H4163 a p) (Set.Ici 0) volume := by
  sorry

theorem proof_gap_exercise_4163_17 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ) :
  ∀ a : ℝ, a > 0 -> p = (1 / 2 : ℝ) ->
    ¬ MeasureTheory.IntegrableOn (fun x : ℝ => 1 / Real.sqrt (a ^ (2 : ℕ) + x ^ (2 : ℕ))) (Set.Ici 0) volume := by
  sorry

theorem proof_gap_exercise_4163_18 (p : ℝ) (I J : WithTop ℝ) (phi : ℝ -> ℝ -> ℝ)
  (hequiv : I < ⊤ ↔ J < ⊤) :
  p ∈ {p : ℝ | p > (1 / 2 : ℝ)} ↔ I < ⊤ := by
  sorry
