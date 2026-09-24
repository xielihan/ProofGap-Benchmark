import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

namespace Exercise4284

abbrev Point3 := ℝ × ℝ × ℝ

axiom VectorCurveInt : {α β : Type} → α → β → ℝ
axiom diff3 : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ

-- Exercise 4284, gap 1
theorem proof_gap_exercise_4284_1
  (C : Point3 × Point3)
  (F : ℝ → ℝ → ℝ → ℝ)
  (hC_mem : C ∈ (Set.univ : Set (Point3 × Point3)))
  (hC : C = (((1 : ℝ), (1 : ℝ), (1 : ℝ)), ((2 : ℝ), (3 : ℝ), (-4 : ℝ))))
  (hF : F = fun x y z : ℝ => (1 / 2 : ℝ) * x ^ (2 : ℕ) + (1 / 3 : ℝ) * y ^ (3 : ℕ) -
    (1 / 4 : ℝ) * z ^ (4 : ℕ)) :
  VectorCurveInt C
      ((fun x y z : ℝ => x) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => y ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => y) -
        (fun x y z : ℝ => z ^ (3 : ℕ)) * diff3 (fun x y z : ℝ => z)) =
    F 2 3 (-4) - F 1 1 1 := by
  sorry

-- Exercise 4284, gap 2
theorem proof_gap_exercise_4284_2
  (C : Point3 × Point3)
  (F : ℝ → ℝ → ℝ → ℝ)
  (hC_mem : C ∈ (Set.univ : Set (Point3 × Point3)))
  (hC : C = (((1 : ℝ), (1 : ℝ), (1 : ℝ)), ((2 : ℝ), (3 : ℝ), (-4 : ℝ))))
  (hF : F = fun x y z : ℝ => (1 / 2 : ℝ) * x ^ (2 : ℕ) + (1 / 3 : ℝ) * y ^ (3 : ℕ) -
    (1 / 4 : ℝ) * z ^ (4 : ℕ))
  (h1 : VectorCurveInt C
      ((fun x y z : ℝ => x) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => y ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => y) -
        (fun x y z : ℝ => z ^ (3 : ℕ)) * diff3 (fun x y z : ℝ => z)) =
    F 2 3 (-4) - F 1 1 1) :
  F 2 3 (-4) - F 1 1 1 = -(643 / 12 : ℝ) := by
  sorry

-- Exercise 4284, gap 3
theorem proof_gap_exercise_4284_3
  (C : Point3 × Point3)
  (F : ℝ → ℝ → ℝ → ℝ)
  (hC_mem : C ∈ (Set.univ : Set (Point3 × Point3)))
  (hC : C = (((1 : ℝ), (1 : ℝ), (1 : ℝ)), ((2 : ℝ), (3 : ℝ), (-4 : ℝ))))
  (hF : F = fun x y z : ℝ => (1 / 2 : ℝ) * x ^ (2 : ℕ) + (1 / 3 : ℝ) * y ^ (3 : ℕ) -
    (1 / 4 : ℝ) * z ^ (4 : ℕ))
  (h1 : VectorCurveInt C
      ((fun x y z : ℝ => x) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => y ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => y) -
        (fun x y z : ℝ => z ^ (3 : ℕ)) * diff3 (fun x y z : ℝ => z)) =
    F 2 3 (-4) - F 1 1 1)
  (h2 : F 2 3 (-4) - F 1 1 1 = -(643 / 12 : ℝ)) :
  VectorCurveInt C
      ((fun x y z : ℝ => x) * diff3 (fun x y z : ℝ => x) +
        (fun x y z : ℝ => y ^ (2 : ℕ)) * diff3 (fun x y z : ℝ => y) -
        (fun x y z : ℝ => z ^ (3 : ℕ)) * diff3 (fun x y z : ℝ => z)) =
    -(643 / 12 : ℝ) := by
  sorry

end Exercise4284
