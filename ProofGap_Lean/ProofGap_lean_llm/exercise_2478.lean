import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable abbrev lpSqrt (x : ℝ) : ℝ := Real.sqrt x
noncomputable abbrev lpArcInt (a b : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in a..b, f x

-- exercise: exercise_2478
-- Exercise 2478, gap 1
theorem proof_gap_exercise_2478_1 (a : ℝ) (y1 y2 : ℝ -> ℝ) (Vx : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hV : Vx ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a -> y1 x = (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a -> y2 x = (x - lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a ->
    y1 x = (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2 := by
  sorry

-- Exercise 2478, gap 2
theorem proof_gap_exercise_2478_2 (a : ℝ) (y1 y2 : ℝ -> ℝ) (Vx : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hV : Vx ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a -> y1 x = (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a -> y2 x = (x - lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2)
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a -> y1 x = (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a ->
    y2 x = (x - lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2 := by
  sorry

-- Exercise 2478, gap 3
theorem proof_gap_exercise_2478_3 (a : ℝ) (y1 y2 : ℝ -> ℝ) (Vx : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hV : Vx ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a -> y1 x = (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ -(2 /. lpSqrt 3) * a ≤ x ∧ x ≤ (2 /. lpSqrt 3) * a -> y2 x = (x - lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) /. 2)
  : Function.support y1 = Set.Icc (-(2 /. lpSqrt 3) * a) ((2 /. lpSqrt 3) * a) := by
  sorry

-- Exercise 2478, gap 4
theorem proof_gap_exercise_2478_4 (a : ℝ) (y1 y2 : ℝ -> ℝ) (Vx : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hV : Vx ∈ (Set.univ : Set ℝ))
  (h9 : Function.support y1 = Set.Icc (-(2 /. lpSqrt 3) * a) ((2 /. lpSqrt 3) * a))
  (h10 : Vx = (Real.pi /. 2) * lpArcInt 0 a (fun x => 4 * a ^ 2 - 2 * x ^ 2 + 2 * x * lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) + 2 * Real.pi * lpArcInt a ((2 /. lpSqrt 3) * a) (fun x => x * lpSqrt (4 * a ^ 2 - 3 * x ^ 2)))
  : Vx = 2 * (Real.pi * lpArcInt 0 a (fun x => (1 /. 4) * (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2) +
      Real.pi * lpArcInt a ((2 /. lpSqrt 3) * a)
        (fun x => (1 /. 4) * (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2 -
          (1 /. 4) * (x - lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2)) := by
  sorry

-- Exercise 2478, gap 5
theorem proof_gap_exercise_2478_5 (a : ℝ) (y1 y2 : ℝ -> ℝ) (Vx : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hV : Vx ∈ (Set.univ : Set ℝ))
  (h10 : Vx = 2 * (Real.pi * lpArcInt 0 a (fun x => (1 /. 4) * (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2) + Real.pi * lpArcInt a ((2 /. lpSqrt 3) * a) (fun x => (1 /. 4) * (x + lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2 - (1 /. 4) * (x - lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2)))
  : Vx = (Real.pi /. 2) * lpArcInt 0 a (fun x => 4 * a ^ 2 - 2 * x ^ 2 + 2 * x * lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) +
      2 * Real.pi * lpArcInt a ((2 /. lpSqrt 3) * a) (fun x => x * lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) := by
  sorry

-- Exercise 2478, gap 6
theorem proof_gap_exercise_2478_6 (a : ℝ) (y1 y2 : ℝ -> ℝ) (Vx : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hV : Vx ∈ (Set.univ : Set ℝ))
  (h11 : Vx = (Real.pi /. 2) * lpArcInt 0 a (fun x => 4 * a ^ 2 - 2 * x ^ 2 + 2 * x * lpSqrt (4 * a ^ 2 - 3 * x ^ 2)) + 2 * Real.pi * lpArcInt a ((2 /. lpSqrt 3) * a) (fun x => x * lpSqrt (4 * a ^ 2 - 3 * x ^ 2)))
  : Vx = (8 /. 3) * Real.pi * a ^ 3 := by
  sorry
