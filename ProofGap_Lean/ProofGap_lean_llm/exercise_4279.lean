import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

namespace Exercise4279

abbrev Point3 := ℝ × ℝ × ℝ

axiom VectorCurveInt : {α β : Type} → α → β → ℝ
axiom DefInt : ℝ → ℝ → (ℝ → ℝ) → ℝ
axiom diff1 : (ℝ → ℝ) → ℝ
axiom diff3 : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ

-- Exercise 4279, gap 1
theorem proof_gap_exercise_4279_1
  (C : ℝ → Point3)
  (x y z : ℝ → ℝ)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 1 →
    x t = t ∧ y t = t ^ (2 : ℕ) ∧ z t = t ^ (3 : ℕ)) :
  VectorCurveInt C
      ((fun x y z : ℝ => y ^ (2 : ℕ) - z ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => 2 * y * z) * diff3 (fun x y z : ℝ => y) -
        (fun x y z : ℝ => x ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => z)) =
    DefInt 0 1
      (fun t : ℝ =>
        (t ^ (4 : ℕ) - t ^ (6 : ℕ) + 2 * t ^ (2 : ℕ) * t ^ (3 : ℕ) * 2 * t -
            t ^ (2 : ℕ) * 3 * t ^ (2 : ℕ)) *
          diff1 (fun t : ℝ => t)) := by
  sorry

-- Exercise 4279, gap 2
theorem proof_gap_exercise_4279_2
  (C : ℝ → Point3)
  (x y z : ℝ → ℝ)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 1 →
    x t = t ∧ y t = t ^ (2 : ℕ) ∧ z t = t ^ (3 : ℕ))
  (h1 : VectorCurveInt C
      ((fun x y z : ℝ => y ^ (2 : ℕ) - z ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => 2 * y * z) * diff3 (fun x y z : ℝ => y) -
        (fun x y z : ℝ => x ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => z)) =
    DefInt 0 1
      (fun t : ℝ =>
        (t ^ (4 : ℕ) - t ^ (6 : ℕ) + 2 * t ^ (2 : ℕ) * t ^ (3 : ℕ) * 2 * t -
            t ^ (2 : ℕ) * 3 * t ^ (2 : ℕ)) *
          diff1 (fun t : ℝ => t))) :
  DefInt 0 1
      (fun t : ℝ =>
        (t ^ (4 : ℕ) - t ^ (6 : ℕ) + 2 * t ^ (2 : ℕ) * t ^ (3 : ℕ) * 2 * t -
            t ^ (2 : ℕ) * 3 * t ^ (2 : ℕ)) *
          diff1 (fun t : ℝ => t)) =
    DefInt 0 1
      (fun t : ℝ => (3 * t ^ (6 : ℕ) - 2 * t ^ (5 : ℕ)) * diff1 (fun t : ℝ => t)) := by
  sorry

-- Exercise 4279, gap 3
theorem proof_gap_exercise_4279_3
  (C : ℝ → Point3)
  (x y z : ℝ → ℝ)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 1 →
    x t = t ∧ y t = t ^ (2 : ℕ) ∧ z t = t ^ (3 : ℕ))
  (h1 : VectorCurveInt C
      ((fun x y z : ℝ => y ^ (2 : ℕ) - z ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => 2 * y * z) * diff3 (fun x y z : ℝ => y) -
        (fun x y z : ℝ => x ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => z)) =
    DefInt 0 1
      (fun t : ℝ =>
        (t ^ (4 : ℕ) - t ^ (6 : ℕ) + 2 * t ^ (2 : ℕ) * t ^ (3 : ℕ) * 2 * t -
            t ^ (2 : ℕ) * 3 * t ^ (2 : ℕ)) *
          diff1 (fun t : ℝ => t)))
  (h2 : DefInt 0 1
      (fun t : ℝ =>
        (t ^ (4 : ℕ) - t ^ (6 : ℕ) + 2 * t ^ (2 : ℕ) * t ^ (3 : ℕ) * 2 * t -
            t ^ (2 : ℕ) * 3 * t ^ (2 : ℕ)) *
          diff1 (fun t : ℝ => t)) =
    DefInt 0 1
      (fun t : ℝ => (3 * t ^ (6 : ℕ) - 2 * t ^ (5 : ℕ)) * diff1 (fun t : ℝ => t))) :
  VectorCurveInt C
      ((fun x y z : ℝ => y ^ (2 : ℕ) - z ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => 2 * y * z) * diff3 (fun x y z : ℝ => y) -
        (fun x y z : ℝ => x ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => z)) =
    (1 / 35 : ℝ) := by
  sorry

end Exercise4279
