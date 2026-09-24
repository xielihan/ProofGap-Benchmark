import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

abbrev ScalarField := ℝ -> ℝ -> ℝ -> ℝ

noncomputable def FunDeri (f : ScalarField) (i k : ℕ) : ScalarField := by
  classical
  exact fun x y z =>
    match i with
    | 1 => iteratedDeriv k (fun t => f t y z) x
    | 2 => iteratedDeriv k (fun t => f x t z) y
    | _ => iteratedDeriv k (fun t => f x y t) z

def FuncOfClassKOn (u : ScalarField) (D : Set (ℝ × ℝ × ℝ)) (k : ℕ) : Prop :=
  ContDiffOn ℝ k (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) D

-- exercise: exercise_3350

variable (u f : ScalarField) (D : Set (ℝ × ℝ × ℝ)) (l : ℝ × ℝ × ℝ)
variable (α β γ x y z : ℝ)
variable (h_point : (x, y, z) ∈ D)
variable (h_u : u = f)
variable (h_smooth : FuncOfClassKOn u D 2)
variable (h_dir : Real.cos α ^ 2 + Real.cos β ^ 2 + Real.cos γ ^ 2 = 1)

-- source gap 1
theorem proof_gap_exercise_3350_1 :
  FunDeri u 1 1 x y z =
    FunDeri u 1 1 x y z * Real.cos α +
    FunDeri u 2 1 x y z * Real.cos β +
    FunDeri u 3 1 x y z * Real.cos γ := by
  sorry

-- source gap 2
theorem proof_gap_exercise_3350_2
  (h_first : FunDeri u 1 1 x y z =
    FunDeri u 1 1 x y z * Real.cos α +
    FunDeri u 2 1 x y z * Real.cos β +
    FunDeri u 3 1 x y z * Real.cos γ) :
  FunDeri u 1 2 x y z =
    (FunDeri u 1 2 x y z * Real.cos α +
      FunDeri (FunDeri u 2 1) 1 1 x y z * Real.cos β +
      FunDeri (FunDeri u 3 1) 1 1 x y z * Real.cos γ) * Real.cos α +
    (FunDeri (FunDeri u 1 1) 2 1 x y z * Real.cos α +
      FunDeri u 2 2 x y z * Real.cos β +
      FunDeri (FunDeri u 3 1) 2 1 x y z * Real.cos γ) * Real.cos β +
    (FunDeri (FunDeri u 1 1) 3 1 x y z * Real.cos α +
      FunDeri (FunDeri u 2 1) 3 1 x y z * Real.cos β +
      FunDeri u 3 2 x y z * Real.cos γ) * Real.cos γ := by
  sorry

-- source gap 3
theorem proof_gap_exercise_3350_3
  (h_second_expand : FunDeri u 1 2 x y z =
    (FunDeri u 1 2 x y z * Real.cos α +
      FunDeri (FunDeri u 2 1) 1 1 x y z * Real.cos β +
      FunDeri (FunDeri u 3 1) 1 1 x y z * Real.cos γ) * Real.cos α +
    (FunDeri (FunDeri u 1 1) 2 1 x y z * Real.cos α +
      FunDeri u 2 2 x y z * Real.cos β +
      FunDeri (FunDeri u 3 1) 2 1 x y z * Real.cos γ) * Real.cos β +
    (FunDeri (FunDeri u 1 1) 3 1 x y z * Real.cos α +
      FunDeri (FunDeri u 2 1) 3 1 x y z * Real.cos β +
      FunDeri u 3 2 x y z * Real.cos γ) * Real.cos γ) :
  FunDeri u 1 2 x y z =
    FunDeri u 1 2 x y z * Real.cos α ^ 2 +
    FunDeri u 2 2 x y z * Real.cos β ^ 2 +
    FunDeri u 3 2 x y z * Real.cos γ ^ 2 +
    2 * FunDeri (FunDeri u 1 1) 2 1 x y z * Real.cos α * Real.cos β +
    2 * FunDeri (FunDeri u 2 1) 3 1 x y z * Real.cos β * Real.cos γ +
    2 * FunDeri (FunDeri u 3 1) 1 1 x y z * Real.cos γ * Real.cos α := by
  sorry
