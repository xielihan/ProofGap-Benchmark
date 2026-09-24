import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def evalOn (F : ℝ → ℝ) (a b : ℝ) : ℝ := F b - F a

-- exercise: exercise_2489

theorem proof_gap_exercise_2489_1
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  : ∃ y_x : ℝ → ℝ, (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x ≤ x_0 →
    Real.sqrt (1 + (deriv y_x x) ^ (2 : ℕ)) = Real.sqrt (p + 2 * x) /. Real.sqrt (2 * x)) := by
  sorry

theorem proof_gap_exercise_2489_2
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  (h6 : ∃ y_x : ℝ → ℝ, ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x ≤ x_0 →
    Real.sqrt (1 + (deriv y_x x) ^ (2 : ℕ)) = Real.sqrt (p + 2 * x) /. Real.sqrt (2 * x))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 →
    P_x = 2 * Real.pi * ∫ x in (0 : ℝ)..x_0, Real.sqrt (2 * p * x) * (Real.sqrt (p + 2 * x) /. Real.sqrt (2 * x)) := by
  sorry

theorem proof_gap_exercise_2489_3
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  (h6 : ∃ y_x : ℝ → ℝ, ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x ∧ x ≤ x_0 → Real.sqrt (1 + (deriv y_x x) ^ (2 : ℕ)) = Real.sqrt (p + 2 * x) /. Real.sqrt (2 * x))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → P_x = 2 * Real.pi * ∫ x in (0 : ℝ)..x_0, Real.sqrt (2 * p * x) * (Real.sqrt (p + 2 * x) /. Real.sqrt (2 * x)))
  : P_x = (2 * Real.pi /. 3) * ((2 * x_0 + p) * Real.sqrt (2 * p * x_0 + p ^ (2 : ℕ)) - p ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_2489_4
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  (h6 : P_x = (2 * Real.pi /. 3) * ((2 * x_0 + p) * Real.sqrt (2 * p * x_0 + p ^ (2 : ℕ)) - p ^ (2 : ℕ)))
  : ∃ x_y : ℝ → ℝ, (∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) →
    Real.sqrt (1 + (deriv x_y y) ^ (2 : ℕ)) = Real.sqrt (p ^ (2 : ℕ) + y ^ (2 : ℕ)) /. p) := by
  sorry

theorem proof_gap_exercise_2489_5
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  (h6 : ∃ x_y : ℝ → ℝ, ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) →
    Real.sqrt (1 + (deriv x_y y) ^ (2 : ℕ)) = Real.sqrt (p ^ (2 : ℕ) + y ^ (2 : ℕ)) /. p)
  : ∃ x_y : ℝ → ℝ, (∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) →
    P_y = 4 * Real.pi * ∫ y in (0 : ℝ)..(Real.sqrt (2 * p * x_0)), x_y y * Real.sqrt (1 + (deriv x_y y) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2489_6
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  (h6 : ∃ x_y : ℝ → ℝ, ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) → P_y = 4 * Real.pi * ∫ y in (0 : ℝ)..(Real.sqrt (2 * p * x_0)), x_y y * Real.sqrt (1 + (deriv x_y y) ^ (2 : ℕ)))
  : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) →
    P_y = 4 * Real.pi * ∫ y in (0 : ℝ)..(Real.sqrt (2 * p * x_0)), (y ^ (2 : ℕ) /. (2 * p)) * (Real.sqrt (p ^ (2 : ℕ) + y ^ (2 : ℕ)) /. p) := by
  sorry

theorem proof_gap_exercise_2489_7
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  (h6 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) → P_y = 4 * Real.pi * ∫ y in (0 : ℝ)..(Real.sqrt (2 * p * x_0)), (y ^ (2 : ℕ) /. (2 * p)) * (Real.sqrt (p ^ (2 : ℕ) + y ^ (2 : ℕ)) /. p))
  : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) →
    P_y = ((2 * Real.pi) /. (p ^ (2 : ℕ))) * ∫ y in (0 : ℝ)..(Real.sqrt (2 * p * x_0)), y ^ (2 : ℕ) * Real.sqrt (p ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_2489_8
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  (h6 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) → P_y = ((2 * Real.pi) /. (p ^ (2 : ℕ))) * ∫ y in (0 : ℝ)..(Real.sqrt (2 * p * x_0)), y ^ (2 : ℕ) * Real.sqrt (p ^ (2 : ℕ) + y ^ (2 : ℕ)))
  : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) →
    P_y = evalOn (fun y => ((2 * Real.pi) /. (p ^ (2 : ℕ))) * (((y * (2 * y ^ (2 : ℕ) + p ^ (2 : ℕ))) /. 8) * Real.sqrt (p ^ (2 : ℕ) + y ^ (2 : ℕ)) - (p ^ (4 : ℕ) /. 8) * Real.log (y + Real.sqrt (y ^ (2 : ℕ) + p ^ (2 : ℕ))))) 0 (Real.sqrt (2 * p * x_0)) := by
  sorry

theorem proof_gap_exercise_2489_9
  (p x_0 P_x P_y : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ) ∧ p > 0)
  (h2 : x_0 ∈ (Set.univ : Set ℝ) ∧ x_0 ≥ 0)
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : P_y ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ x_0 → y ^ (2 : ℕ) = 2 * p * x)
  (h6 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ 0 ≤ y ∧ y ≤ Real.sqrt (2 * p * x_0) → P_y = evalOn (fun y => ((2 * Real.pi) /. (p ^ (2 : ℕ))) * (((y * (2 * y ^ (2 : ℕ) + p ^ (2 : ℕ))) /. 8) * Real.sqrt (p ^ (2 : ℕ) + y ^ (2 : ℕ)) - (p ^ (4 : ℕ) /. 8) * Real.log (y + Real.sqrt (y ^ (2 : ℕ) + p ^ (2 : ℕ))))) 0 (Real.sqrt (2 * p * x_0)))
  : P_y = (Real.pi /. 4) * ((p + 4 * x_0) * Real.sqrt (2 * x_0 * (p + 2 * x_0)) - p ^ (2 : ℕ) * Real.log ((Real.sqrt (2 * x_0) + Real.sqrt (p + 2 * x_0)) /. Real.sqrt p)) := by
  sorry
