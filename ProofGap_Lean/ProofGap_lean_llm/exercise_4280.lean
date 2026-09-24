import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

namespace Exercise4280

abbrev Point3 := ℝ × ℝ × ℝ

axiom VectorCurveInt : {α β : Type} → α → β → ℝ
axiom DefInt : ℝ → ℝ → (ℝ → ℝ) → ℝ
axiom diff1 : (ℝ → ℝ) → ℝ
axiom diff3 : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ
axiom evalOn : (ℝ → ℝ) → ℝ → ℝ → ℝ

-- Exercise 4280, gap 1
theorem proof_gap_exercise_4280_1
  (C : ℝ → Point3)
  (x y z : ℝ → ℝ)
  (a b : ℝ)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
    x t = a * Real.cos t ∧ y t = a * Real.sin t ∧ z t = b * t) :
  VectorCurveInt C
      ((fun x y z : ℝ => y) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => z) * diff3 (fun x y z : ℝ => y) +
        (fun x y z : ℝ => x) * diff3 (fun x y z : ℝ => z)) =
    DefInt 0 (2 * Real.pi)
      (fun t : ℝ =>
        (-a ^ (2 : ℕ) * Real.sin t * Real.sin t + a * b * t * Real.cos t +
            a * b * Real.cos t) *
          diff1 (fun t : ℝ => t)) := by
  sorry

-- Exercise 4280, gap 2
theorem proof_gap_exercise_4280_2
  (C : ℝ → Point3)
  (x y z : ℝ → ℝ)
  (a b : ℝ)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
    x t = a * Real.cos t ∧ y t = a * Real.sin t ∧ z t = b * t)
  (h1 : VectorCurveInt C
      ((fun x y z : ℝ => y) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => z) * diff3 (fun x y z : ℝ => y) +
        (fun x y z : ℝ => x) * diff3 (fun x y z : ℝ => z)) =
    DefInt 0 (2 * Real.pi)
      (fun t : ℝ =>
        (-a ^ (2 : ℕ) * Real.sin t * Real.sin t + a * b * t * Real.cos t +
            a * b * Real.cos t) *
          diff1 (fun t : ℝ => t))) :
  DefInt 0 (2 * Real.pi)
      (fun t : ℝ =>
        (-a ^ (2 : ℕ) * Real.sin t * Real.sin t + a * b * t * Real.cos t +
            a * b * Real.cos t) *
          diff1 (fun t : ℝ => t)) =
    evalOn
      (fun t : ℝ =>
        -(a ^ (2 : ℕ) * t) / 2 + (a ^ (2 : ℕ) * Real.sin (2 * t)) / 4 +
          a * b * t * Real.sin t + a * b * Real.cos t + a * b * Real.sin t)
      0 (2 * Real.pi) := by
  sorry

-- Exercise 4280, gap 3
theorem proof_gap_exercise_4280_3
  (C : ℝ → Point3)
  (x y z : ℝ → ℝ)
  (a b : ℝ)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
    x t = a * Real.cos t ∧ y t = a * Real.sin t ∧ z t = b * t)
  (h1 : VectorCurveInt C
      ((fun x y z : ℝ => y) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => z) * diff3 (fun x y z : ℝ => y) +
        (fun x y z : ℝ => x) * diff3 (fun x y z : ℝ => z)) =
    DefInt 0 (2 * Real.pi)
      (fun t : ℝ =>
        (-a ^ (2 : ℕ) * Real.sin t * Real.sin t + a * b * t * Real.cos t +
            a * b * Real.cos t) *
          diff1 (fun t : ℝ => t)))
  (h2 : DefInt 0 (2 * Real.pi)
      (fun t : ℝ =>
        (-a ^ (2 : ℕ) * Real.sin t * Real.sin t + a * b * t * Real.cos t +
            a * b * Real.cos t) *
          diff1 (fun t : ℝ => t)) =
    evalOn
      (fun t : ℝ =>
        -(a ^ (2 : ℕ) * t) / 2 + (a ^ (2 : ℕ) * Real.sin (2 * t)) / 4 +
          a * b * t * Real.sin t + a * b * Real.cos t + a * b * Real.sin t)
      0 (2 * Real.pi)) :
  VectorCurveInt C
      ((fun x y z : ℝ => y) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => z) * diff3 (fun x y z : ℝ => y) +
        (fun x y z : ℝ => x) * diff3 (fun x y z : ℝ => z)) =
    -Real.pi * a ^ (2 : ℕ) := by
  sorry

end Exercise4280
