import Mathlib

set_option linter.style.longLine false

open scoped Topology
open Filter

noncomputable abbrev D4161 : Set (ℝ × ℝ) := {q | q.1 ^ (2 : ℕ) + q.2 ^ (2 : ℕ) > 1}
noncomputable abbrev f4161 (phi : ℝ -> ℝ -> ℝ) (p : ℝ) : ℝ × ℝ -> ℝ :=
  fun q => phi q.1 q.2 / ((q.1 ^ (2 : ℕ) + q.2 ^ (2 : ℕ)) ^ p)
noncomputable abbrev g4161 (p : ℝ) : ℝ × ℝ -> ℝ :=
  fun q => 1 / ((q.1 ^ (2 : ℕ) + q.2 ^ (2 : ℕ)) ^ p)

-- exercise: exercise_4161

theorem proof_gap_exercise_4161_1
  (phi : ℝ -> ℝ -> ℝ) (m M p : ℝ) (hm : m > 0) (hM : M > 0)
  (hbound : ∀ x y : ℝ, (x, y) ∈ D4161 -> m ≤ |phi x y| ∧ |phi x y| ≤ M) :
  ∀ x y : ℝ, (x, y) ∈ D4161 ->
    m / ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) ≤ |phi x y / ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p)| ∧
    |phi x y / ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p)| ≤ M / ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) := by
  sorry

theorem proof_gap_exercise_4161_2
  (phi : ℝ -> ℝ -> ℝ) (m M p : ℝ) (hm : m > 0) (hM : M > 0)
  (hbound : ∀ x y : ℝ, (x, y) ∈ D4161 -> m ≤ |phi x y| ∧ |phi x y| ≤ M)
  (hcmp : ∀ x y : ℝ, (x, y) ∈ D4161 ->
    m / ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p) ≤ |phi x y / ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p)| ∧
    |phi x y / ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p)| ≤ M / ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ p)) :
  MeasureTheory.IntegrableOn (f4161 phi p) D4161 volume ↔ MeasureTheory.IntegrableOn (g4161 p) D4161 volume := by
  sorry

theorem proof_gap_exercise_4161_3
  (phi : ℝ -> ℝ -> ℝ) (m M p : ℝ) :
  ∀ x y r : ℝ, r ≥ 1 ->
    ∫ q in D4161, g4161 p q = (∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ)) * (∫ r in (1 : ℝ)..r, r / (r ^ (2 * p))) := by
  sorry

theorem proof_gap_exercise_4161_4
  (phi : ℝ -> ℝ -> ℝ) (m M p : ℝ) :
  ∀ r : ℝ, r ≥ 1 ->
    (∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ)) * (∫ r in (1 : ℝ)..r, r / (r ^ (2 * p))) =
      if p > 1 then Real.pi / (p - 1) else 0 := by
  sorry

theorem proof_gap_exercise_4161_5
  (phi : ℝ -> ℝ -> ℝ) (m M p : ℝ)
  (hsim : MeasureTheory.IntegrableOn (f4161 phi p) D4161 volume ↔ MeasureTheory.IntegrableOn (g4161 p) D4161 volume) :
  p > 1 -> MeasureTheory.IntegrableOn (f4161 phi p) D4161 volume := by
  sorry

theorem proof_gap_exercise_4161_6
  (phi : ℝ -> ℝ -> ℝ) (m M p : ℝ)
  (hsim : MeasureTheory.IntegrableOn (f4161 phi p) D4161 volume ↔ MeasureTheory.IntegrableOn (g4161 p) D4161 volume) :
  p ≤ 1 -> ¬ MeasureTheory.IntegrableOn (f4161 phi p) D4161 volume := by
  sorry

theorem proof_gap_exercise_4161_7
  (phi : ℝ -> ℝ -> ℝ) (m M p : ℝ)
  (hconv : p > 1 -> MeasureTheory.IntegrableOn (f4161 phi p) D4161 volume)
  (hdiv : p ≤ 1 -> ¬ MeasureTheory.IntegrableOn (f4161 phi p) D4161 volume) :
  p ∈ {p : ℝ | p > 1} ↔ MeasureTheory.IntegrableOn (f4161 phi p) D4161 volume := by
  sorry
