import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def evalOn (F : ℝ → ℝ) (a b : ℝ) : ℝ := F b - F a

-- exercise: exercise_2492

theorem proof_gap_exercise_2492_1
  (a P_x : ℝ) (y : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a ∧ y x > 0 → deriv y x = -Real.rpow (y x /. x) (1 /. 3))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a →
    Real.rpow (y x) (2 /. 3) + Real.rpow x (2 /. 3) = Real.rpow a (2 /. 3) := by
  sorry

theorem proof_gap_exercise_2492_2
  (a P_x : ℝ) (y : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a → Real.rpow (y x) (2 /. 3) + Real.rpow x (2 /. 3) = Real.rpow a (2 /. 3))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a ∧ y x > 0 → Real.sqrt (1 + (deriv y x) ^ (2 : ℕ)) = Real.rpow a (1 /. 3) /. Real.rpow x (1 /. 3))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a ∧ y x > 0 →
      deriv y x = -Real.rpow (y x /. x) (1 /. 3) := by
  sorry

theorem proof_gap_exercise_2492_3
  (a P_x : ℝ) (y : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a → Real.rpow (y x) (2 /. 3) + Real.rpow x (2 /. 3) = Real.rpow a (2 /. 3))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a ∧ y x > 0 → deriv y x = -Real.rpow (y x /. x) (1 /. 3))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a ∧ y x > 0 →
    Real.sqrt (1 + (deriv y x) ^ (2 : ℕ)) = Real.rpow a (1 /. 3) /. Real.rpow x (1 /. 3) := by
  sorry

theorem proof_gap_exercise_2492_4
  (a P_x : ℝ) (y : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a → Real.rpow (y x) (2 /. 3) + Real.rpow x (2 /. 3) = Real.rpow a (2 /. 3))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a ∧ y x > 0 → deriv y x = -Real.rpow (y x /. x) (1 /. 3))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a ∧ y x > 0 → Real.sqrt (1 + (deriv y x) ^ (2 : ℕ)) = Real.rpow a (1 /. 3) /. Real.rpow x (1 /. 3))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → P_x = evalOn (fun x => - ((12 * Real.pi * Real.rpow a (1 /. 3)) /. 5) * Real.rpow (Real.rpow a (2 /. 3) - Real.rpow x (2 /. 3)) (5 /. 2)) 0 a)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a →
    P_x = 2 * 2 * Real.pi * ∫ x in (0 : ℝ)..a, Real.rpow (Real.rpow a (2 /. 3) - Real.rpow x (2 /. 3)) (3 /. 2) * (Real.rpow a (1 /. 3) /. Real.rpow x (1 /. 3)) := by
  sorry

theorem proof_gap_exercise_2492_5
  (a P_x : ℝ) (y : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a → Real.rpow (y x) (2 /. 3) + Real.rpow x (2 /. 3) = Real.rpow a (2 /. 3))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a → P_x = 2 * 2 * Real.pi * ∫ x in (0 : ℝ)..a, Real.rpow (Real.rpow a (2 /. 3) - Real.rpow x (2 /. 3)) (3 /. 2) * (Real.rpow a (1 /. 3) /. Real.rpow x (1 /. 3)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x = evalOn (fun x => - ((12 * Real.pi * Real.rpow a (1 /. 3)) /. 5) * Real.rpow (Real.rpow a (2 /. 3) - Real.rpow x (2 /. 3)) (5 /. 2)) 0 a := by
  sorry

theorem proof_gap_exercise_2492_6
  (a P_x : ℝ) (y : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x < a → Real.rpow (y x) (2 /. 3) + Real.rpow x (2 /. 3) = Real.rpow a (2 /. 3))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → P_x = evalOn (fun x => - ((12 * Real.pi * Real.rpow a (1 /. 3)) /. 5) * Real.rpow (Real.rpow a (2 /. 3) - Real.rpow x (2 /. 3)) (5 /. 2)) 0 a)
  : P_x = (12 * Real.pi * a ^ (2 : ℕ)) /. 5 := by
  sorry
