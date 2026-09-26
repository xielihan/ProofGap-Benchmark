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

-- exercise: exercise_3557

def ParaboloidNormal (x y : ℝ) : V3 := (2 * x, 2 * y, 1)
def CrossNormalDiff (x y x1 y1 : ℝ) : V3 := (2 * (y - y1), 2 * (x1 - x), 4 * (x * y1 - x1 * y))
def angleSinByCross (φ : ℝ) (n n1 w : V3) : Prop := Real.sin φ = ‖₃w‖ / (‖₃n‖ * ‖₃n1‖)

theorem proof_gap_exercise_3557_1
  (δ : ℝ) (w : V3)
  : ∀ n : V3, ∀ x y : ℝ, n = ParaboloidNormal x y := by
  sorry

theorem proof_gap_exercise_3557_2
  (δ : ℝ) (w : V3)
  : ∀ n1 : V3, ∀ x1 y1 : ℝ, n1 = ParaboloidNormal x1 y1 := by
  sorry

theorem proof_gap_exercise_3557_3
  (δ : ℝ) (w : V3)
  : ∀ n : V3, ‖₃n‖ ≥ 1 := by
  sorry

theorem proof_gap_exercise_3557_4
  (δ : ℝ) (w : V3)
  : ∀ n1 : V3, ‖₃n1‖ ≥ 1 := by
  sorry

theorem proof_gap_exercise_3557_5
  (δ : ℝ) (w : V3)
  : ∀ φ : ℝ, ∀ n n1 : V3, angleSinByCross φ n n1 w := by
  sorry

theorem proof_gap_exercise_3557_6
  (δ : ℝ) (w : V3)
  : ∀ φ : ℝ, Real.sin φ ≤ ‖₃w‖ := by
  sorry

theorem proof_gap_exercise_3557_7
  (δ : ℝ) (w : V3)
  : ∀ x y x1 y1 : ℝ, ‖₃w‖ = 2 * Real.sqrt ((y - y1) ^ 2 + (x - x1) ^ 2 + 4 * (x * y1 - x1 * y) ^ 2) := by
  sorry

theorem proof_gap_exercise_3557_8
  (δ : ℝ) (w : V3)
  : ∀ x y x1 y1 : ℝ, (x * y1 - x1 * y) ^ 2 = (x * (y1 - y) + y * (x - x1)) ^ 2 := by
  sorry

theorem proof_gap_exercise_3557_9
  (δ : ℝ) (w : V3)
  : ∀ x y x1 y1 : ℝ, 0 ≤ x ∧ x ≤ 1 -> 0 ≤ y ∧ y ≤ 1 -> (x * y1 - x1 * y) ^ 2 ≤ 2 * (x ^ 2 * (y1 - y) ^ 2 + y ^ 2 * (x - x1) ^ 2) := by
  sorry

theorem proof_gap_exercise_3557_10
  (δ : ℝ) (w : V3)
  : ∀ x y x1 y1 : ℝ, 0 ≤ x ∧ x ≤ 1 -> 0 ≤ y ∧ y ≤ 1 -> (x * y1 - x1 * y) ^ 2 ≤ 2 * ((y - y1) ^ 2 + (x - x1) ^ 2) := by
  sorry

theorem proof_gap_exercise_3557_11
  (δ : ℝ) (w : V3)
  : ∀ φ ρ : ℝ, Real.sin φ ≤ 2 * Real.sqrt (ρ ^ 2 + 4 * 2 * ρ ^ 2) := by
  sorry

theorem proof_gap_exercise_3557_12
  (δ : ℝ) (w : V3)
  : ∀ φ ρ : ℝ, Real.sin φ ≤ 6 * ρ := by
  sorry

theorem proof_gap_exercise_3557_13
  (δ : ℝ) (w : V3)
  : ∀ φ : ℝ, Real.sin φ < Real.pi / 180 -> φ < Real.pi / 180 := by
  sorry

theorem proof_gap_exercise_3557_14
  (δ : ℝ) (w : V3)
  : ∀ φ ρ : ℝ, 6 * ρ < Real.pi / 180 -> Real.sin φ < Real.pi / 180 := by
  sorry

theorem proof_gap_exercise_3557_15
  (δ : ℝ) (w : V3)
  : ∀ ρ : ℝ, ρ < Real.pi / 1080 -> 6 * ρ < Real.pi / 180 := by
  sorry

theorem proof_gap_exercise_3557_16
  (δ : ℝ) (w : V3)
  : ∀ ρ : ℝ, δ < Real.pi / 1080 -> ρ < Real.pi / 1080 := by
  sorry

theorem proof_gap_exercise_3557_17
  (δ : ℝ) (w : V3)
  : ∀ φ : ℝ, δ < Real.pi / 1080 -> φ < Real.pi / 180 := by
  sorry

theorem proof_gap_exercise_3557_18
  (δ : ℝ) (w : V3)
  : ∀ φ : ℝ, δ < Real.pi / 1080 ↔ (∀ x y x1 y1 : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ 0 ≤ x1 ∧ x1 ≤ 1 ∧ 0 ≤ y1 ∧ y1 ≤ 1 ∧ Real.sqrt ((x - x1) ^ 2 + (y - y1) ^ 2) ≤ δ -> φ < Real.pi / 180) := by
  sorry
