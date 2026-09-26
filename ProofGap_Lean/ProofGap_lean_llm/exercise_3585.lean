import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

abbrev R2 := ℝ × ℝ
abbrev V3 := ℝ × ℝ × ℝ

def v3dot (u v : V3) : ℝ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2
infixl:70 " ·₃ " => v3dot

noncomputable def v3norm (v : V3) : ℝ := Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)
local notation "‖₃" v "‖" => v3norm v

def smulV3 (a : ℝ) (v : V3) : V3 := (a * v.1, a * v.2.1, a * v.2.2)

noncomputable def eCoord (coord : ℕ) : R2 := if coord = 1 then (1, 0) else (0, 1)

noncomputable def FunDeri : (R2 -> ℝ) -> ℕ -> ℕ -> R2 -> ℝ
  | f, coord, 0 => f
  | f, coord, n + 1 => fun p => fderiv ℝ (FunDeri f coord n) p (eCoord coord)

def approxPow (h : ℝ) (n : ℕ) (actual model : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ |actual - model| ≤ C * |h| ^ n

def diffX (x _y : ℝ) : ℝ := x - 1
def diffY (_x y : ℝ) : ℝ := y - 1

-- exercise: exercise_3585


theorem proof_gap_exercise_3585_1
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri f 1 1 (x, y) = y * Real.rpow x (y - 1) := by
  sorry

theorem proof_gap_exercise_3585_2
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri f 2 1 (x, y) = Real.rpow x y * Real.log x := by
  sorry

theorem proof_gap_exercise_3585_3
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri f 1 2 (x, y) = y * (y - 1) * Real.rpow x (y - 2) := by
  sorry

theorem proof_gap_exercise_3585_4
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri (FunDeri f 1 1) 2 1 (x, y) = Real.rpow x (y - 1) + y * Real.rpow x (y - 1) * Real.log x := by
  sorry

theorem proof_gap_exercise_3585_5
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri f 2 2 (x, y) = Real.rpow x y * (Real.log x) ^ 2 := by
  sorry

theorem proof_gap_exercise_3585_6
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri f 1 3 (x, y) = y * (y - 1) * (y - 2) * Real.rpow x (y - 3) := by
  sorry

theorem proof_gap_exercise_3585_7
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri f 2 3 (x, y) = Real.rpow x y * (Real.log x) ^ 3 := by
  sorry

theorem proof_gap_exercise_3585_8
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri (FunDeri f 1 2) 2 1 (x, y) = (2 * y - 1) * Real.rpow x (y - 2) + y * (y - 1) * Real.rpow x (y - 2) * Real.log x := by
  sorry

theorem proof_gap_exercise_3585_9
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> FunDeri (FunDeri f 1 1) 2 2 (x, y) = y * Real.rpow x (y - 1) * (Real.log x) ^ 2 + 2 * Real.rpow x (y - 1) * Real.log x := by
  sorry

theorem proof_gap_exercise_3585_10
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : f (1, 1) = 1 := by
  sorry

theorem proof_gap_exercise_3585_11
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : FunDeri f 1 1 (1, 1) = 1 := by
  sorry

theorem proof_gap_exercise_3585_12
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : FunDeri f 2 1 (1, 1) = 0 := by
  sorry

theorem proof_gap_exercise_3585_13
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : FunDeri f 1 2 (1, 1) = 0 := by
  sorry

theorem proof_gap_exercise_3585_14
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : FunDeri (FunDeri f 1 1) 2 1 (1, 1) = 1 := by
  sorry

theorem proof_gap_exercise_3585_15
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : FunDeri f 2 2 (1, 1) = 0 := by
  sorry

theorem proof_gap_exercise_3585_16
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ f (x, y) = 1 + x - 1 + (x - 1) * (y - 1) + R2rem (1 + θ * (x - 1), 1 + θ * (y - 1)) := by
  sorry

theorem proof_gap_exercise_3585_17
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x y : ℝ, 0 < x -> R2rem (x, y) = (1 / 6 : ℝ) * (y * (y - 1) * (y - 2) * Real.rpow x (y - 3) * (diffX x y) ^ 3 + 3 * ((2 * y - 1) * Real.rpow x (y - 2) + y * (y - 1) * Real.rpow x (y - 2) * Real.log x) * (diffX x y) ^ 2 * diffY x y + 3 * (y * Real.rpow x (y - 1) * (Real.log x) ^ 2 + 2 * Real.rpow x (y - 1) * Real.log x) * diffX x y * (diffY x y) ^ 2 + Real.rpow x y * (Real.log x) ^ 3 * (diffY x y) ^ 3) := by
  sorry

theorem proof_gap_exercise_3585_18
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ x : ℝ, diffX x y = x - 1 := by
  sorry

theorem proof_gap_exercise_3585_19
  (f R2rem : R2 -> ℝ) (x y : ℝ)
  (hf : ∀ x y : ℝ, 0 < x -> f (x, y) = Real.rpow x y)
  : ∀ y : ℝ, diffY x y = y - 1 := by
  sorry
