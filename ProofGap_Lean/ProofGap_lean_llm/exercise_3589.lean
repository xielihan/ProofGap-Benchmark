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

-- exercise: exercise_3589

def DomainForFivePoint (f : R2 -> ℝ) (x y h : ℝ) : Prop :=
  DifferentiableOn ℝ f {p : R2 | p.1 ∈ Set.Icc (x - |h|) (x + |h|) ∧ p.2 ∈ Set.Icc (y - |h|) (y + |h|)}


theorem proof_gap_exercise_3589_1
  (F f : R2 -> ℝ) (x y h : ℝ)
  (hf4 : ContDiffOn ℝ 4 f {p : R2 | p.1 ∈ Set.Icc (x - |h|) (x + |h|) ∧ p.2 ∈ Set.Icc (y - |h|) (y + |h|)})
  (hF : F (x, y) = (1 / 4 : ℝ) * (f (x + h, y) + f (x, y + h) + f (x - h, y) + f (x, y - h)) - f (x, y))
  : F (x, y) = (1 / 4 : ℝ) * (f (x + h, y) - f (x, y) + f (x, y + h) - f (x, y) + f (x - h, y) - f (x, y) + f (x, y - h) - f (x, y)) := by
  sorry

theorem proof_gap_exercise_3589_2
  (F f : R2 -> ℝ) (x y h : ℝ)
  (hf4 : ContDiffOn ℝ 4 f {p : R2 | p.1 ∈ Set.Icc (x - |h|) (x + |h|) ∧ p.2 ∈ Set.Icc (y - |h|) (y + |h|)})
  (hF : F (x, y) = (1 / 4 : ℝ) * (f (x + h, y) + f (x, y + h) + f (x - h, y) + f (x, y - h)) - f (x, y))
  : approxPow h 5 (f (x + h, y) - f (x, y)) (h * FunDeri f 1 1 (x, y) + (1 / 2 : ℝ) * h ^ 2 * FunDeri f 1 2 (x, y) + (1 / 6 : ℝ) * h ^ 3 * FunDeri f 1 3 (x, y) + (1 / 24 : ℝ) * h ^ 4 * FunDeri f 1 4 (x, y)) := by
  sorry

theorem proof_gap_exercise_3589_3
  (F f : R2 -> ℝ) (x y h : ℝ)
  (hf4 : ContDiffOn ℝ 4 f {p : R2 | p.1 ∈ Set.Icc (x - |h|) (x + |h|) ∧ p.2 ∈ Set.Icc (y - |h|) (y + |h|)})
  (hF : F (x, y) = (1 / 4 : ℝ) * (f (x + h, y) + f (x, y + h) + f (x - h, y) + f (x, y - h)) - f (x, y))
  : approxPow h 5 (f (x - h, y) - f (x, y)) (-h * FunDeri f 1 1 (x, y) + (1 / 2 : ℝ) * h ^ 2 * FunDeri f 1 2 (x, y) - (1 / 6 : ℝ) * h ^ 3 * FunDeri f 1 3 (x, y) + (1 / 24 : ℝ) * h ^ 4 * FunDeri f 1 4 (x, y)) := by
  sorry

theorem proof_gap_exercise_3589_4
  (F f : R2 -> ℝ) (x y h : ℝ)
  (hf4 : ContDiffOn ℝ 4 f {p : R2 | p.1 ∈ Set.Icc (x - |h|) (x + |h|) ∧ p.2 ∈ Set.Icc (y - |h|) (y + |h|)})
  (hF : F (x, y) = (1 / 4 : ℝ) * (f (x + h, y) + f (x, y + h) + f (x - h, y) + f (x, y - h)) - f (x, y))
  : approxPow h 5 (f (x, y + h) - f (x, y)) (h * FunDeri f 2 1 (x, y) + (1 / 2 : ℝ) * h ^ 2 * FunDeri f 2 2 (x, y) + (1 / 6 : ℝ) * h ^ 3 * FunDeri f 2 3 (x, y) + (1 / 24 : ℝ) * h ^ 4 * FunDeri f 2 4 (x, y)) := by
  sorry

theorem proof_gap_exercise_3589_5
  (F f : R2 -> ℝ) (x y h : ℝ)
  (hf4 : ContDiffOn ℝ 4 f {p : R2 | p.1 ∈ Set.Icc (x - |h|) (x + |h|) ∧ p.2 ∈ Set.Icc (y - |h|) (y + |h|)})
  (hF : F (x, y) = (1 / 4 : ℝ) * (f (x + h, y) + f (x, y + h) + f (x - h, y) + f (x, y - h)) - f (x, y))
  : approxPow h 5 (f (x, y - h) - f (x, y)) (-h * FunDeri f 2 1 (x, y) + (1 / 2 : ℝ) * h ^ 2 * FunDeri f 2 2 (x, y) - (1 / 6 : ℝ) * h ^ 3 * FunDeri f 2 3 (x, y) + (1 / 24 : ℝ) * h ^ 4 * FunDeri f 2 4 (x, y)) := by
  sorry

theorem proof_gap_exercise_3589_6
  (F f : R2 -> ℝ) (x y h : ℝ)
  (hf4 : ContDiffOn ℝ 4 f {p : R2 | p.1 ∈ Set.Icc (x - |h|) (x + |h|) ∧ p.2 ∈ Set.Icc (y - |h|) (y + |h|)})
  (hF : F (x, y) = (1 / 4 : ℝ) * (f (x + h, y) + f (x, y + h) + f (x - h, y) + f (x, y - h)) - f (x, y))
  : approxPow h 5 (F (x, y)) ((h ^ 2 / 4 : ℝ) * (FunDeri f 1 2 (x, y) + FunDeri f 2 2 (x, y)) + (h ^ 4 / 48 : ℝ) * (FunDeri f 1 4 (x, y) + FunDeri f 2 4 (x, y))) := by
  sorry
