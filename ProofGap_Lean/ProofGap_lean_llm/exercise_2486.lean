import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def evalOn (F : ℝ → ℝ) (a b : ℝ) : ℝ := F b - F a

-- exercise: exercise_2486

theorem proof_gap_exercise_2486_1
  (y : ℝ → ℝ) (a P_x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → y x = x * Real.sqrt (x /. a))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x = 2 * Real.pi * ∫ x in (0 : ℝ)..a, x * Real.sqrt (x /. a) * Real.sqrt (1 + (9 * x) /. (4 * a)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    Real.sqrt (1 + (deriv y x) ^ (2 : ℕ)) = Real.sqrt (1 + (9 * x) /. (4 * a)) := by
  sorry

theorem proof_gap_exercise_2486_2
  (y : ℝ → ℝ) (a P_x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → y x = x * Real.sqrt (x /. a))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    Real.sqrt (1 + (deriv y x) ^ (2 : ℕ)) = Real.sqrt (1 + (9 * x) /. (4 * a)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x = 2 * Real.pi * ∫ x in (0 : ℝ)..a, x * Real.sqrt (x /. a) * Real.sqrt (1 + (9 * x) /. (4 * a)) := by
  sorry

theorem proof_gap_exercise_2486_3
  (y : ℝ → ℝ) (a P_x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → y x = x * Real.sqrt (x /. a))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    Real.sqrt (1 + (deriv y x) ^ (2 : ℕ)) = Real.sqrt (1 + (9 * x) /. (4 * a)))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x = 2 * Real.pi * ∫ x in (0 : ℝ)..a, x * Real.sqrt (x /. a) * Real.sqrt (1 + (9 * x) /. (4 * a)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x = ((3 * Real.pi) /. a) * ∫ x in (0 : ℝ)..a, x * Real.sqrt (x ^ (2 : ℕ) + (4 * a * x) /. 9) := by
  sorry

theorem proof_gap_exercise_2486_4
  (y : ℝ → ℝ) (a P_x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → y x = x * Real.sqrt (x /. a))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    Real.sqrt (1 + (deriv y x) ^ (2 : ℕ)) = Real.sqrt (1 + (9 * x) /. (4 * a)))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x = 2 * Real.pi * ∫ x in (0 : ℝ)..a, x * Real.sqrt (x /. a) * Real.sqrt (1 + (9 * x) /. (4 * a)))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x = ((3 * Real.pi) /. a) * ∫ x in (0 : ℝ)..a, x * Real.sqrt (x ^ (2 : ℕ) + (4 * a * x) /. 9))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x =
      ((3 * Real.pi) /. a) * ∫ x in (0 : ℝ)..a, (x + (2 * a) /. 9) * Real.sqrt ((x + (2 * a) /. 9) ^ (2 : ℕ) - ((2 * a) /. 9) ^ (2 : ℕ))
      - ((3 * Real.pi) /. a) * ((2 * a) /. 9) * ∫ x in (0 : ℝ)..a, Real.sqrt (x ^ (2 : ℕ) + (4 * a * x) /. 9) := by
  sorry

theorem proof_gap_exercise_2486_5
  (y : ℝ → ℝ) (a P_x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → y x = x * Real.sqrt (x /. a))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → Real.sqrt (1 + (deriv y x) ^ (2 : ℕ)) = Real.sqrt (1 + (9 * x) /. (4 * a)))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → P_x = 2 * Real.pi * ∫ x in (0 : ℝ)..a, x * Real.sqrt (x /. a) * Real.sqrt (1 + (9 * x) /. (4 * a)))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → P_x = ((3 * Real.pi) /. a) * ∫ x in (0 : ℝ)..a, x * Real.sqrt (x ^ (2 : ℕ) + (4 * a * x) /. 9))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → P_x = ((3 * Real.pi) /. a) * ∫ x in (0 : ℝ)..a, (x + (2 * a) /. 9) * Real.sqrt ((x + (2 * a) /. 9) ^ (2 : ℕ) - ((2 * a) /. 9) ^ (2 : ℕ)) - ((3 * Real.pi) /. a) * ((2 * a) /. 9) * ∫ x in (0 : ℝ)..a, Real.sqrt (x ^ (2 : ℕ) + (4 * a * x) /. 9))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a →
    P_x =
      evalOn (fun x => ((3 * Real.pi) /. a) * (1 /. 3) * (x ^ (2 : ℕ) + (4 * a * x) /. 9) ^ (3 : ℕ)) 0 a
      - evalOn (fun x => (2 * Real.pi /. 3) * (((x + (2 * a) /. 9) /. 2) * Real.sqrt (x ^ (2 : ℕ) + (4 * a * x) /. 9) - ((((4 * a ^ (2 : ℕ)) /. 81) /. 2) * Real.log (x + (2 * a) /. 9 - Real.sqrt (x ^ (2 : ℕ) + (4 * a * x) /. 9))))) 0 a := by
  sorry

theorem proof_gap_exercise_2486_6
  (y : ℝ → ℝ) (a P_x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → y x = x * Real.sqrt (x /. a))
  (h4 : P_x = ((4 * Real.pi * a ^ (2 : ℕ)) /. 243) * (21 * Real.sqrt 13 + 2 * Real.log ((3 + Real.sqrt 13) /. 2)))
  : P_x = ((13 * Real.sqrt 13) /. 27) * Real.pi * a ^ (2 : ℕ) - ((11 * Real.sqrt 13) /. 81) * Real.pi * a ^ (2 : ℕ) + ((4 * Real.pi * a ^ (2 : ℕ)) /. 243) * Real.log ((11 + 3 * Real.sqrt 13) /. 2) := by
  sorry

theorem proof_gap_exercise_2486_7
  (y : ℝ → ℝ) (a P_x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (h2 : P_x ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ a → y x = x * Real.sqrt (x /. a))
  (h4 : P_x = ((13 * Real.sqrt 13) /. 27) * Real.pi * a ^ (2 : ℕ) - ((11 * Real.sqrt 13) /. 81) * Real.pi * a ^ (2 : ℕ) + ((4 * Real.pi * a ^ (2 : ℕ)) /. 243) * Real.log ((11 + 3 * Real.sqrt 13) /. 2))
  : P_x = ((4 * Real.pi * a ^ (2 : ℕ)) /. 243) * (21 * Real.sqrt 13 + 2 * Real.log ((3 + Real.sqrt 13) /. 2)) := by
  sorry
