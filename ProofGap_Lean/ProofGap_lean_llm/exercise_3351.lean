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

noncomputable def dirDeri (u : ScalarField) (ell : ℕ -> ℝ) (i order : ℕ) (x y z : ℝ) : ℝ :=
  FunDeri u i order x y z

-- exercise: exercise_3351

variable (u f : ScalarField) (D : Set (ℝ × ℝ × ℝ))
variable (l α β γ : ℕ -> ℝ) (x y z : ℝ)
variable (h_point : (x, y, z) ∈ D)
variable (h_u : u = f)
variable (h_smooth : FuncOfClassKOn u D 2)
variable (h_unit : ∀ i ∈ ({1, 2, 3} : Finset ℕ),
  Real.cos (α i) ^ 2 + Real.cos (β i) ^ 2 + Real.cos (γ i) ^ 2 = 1)
variable (h_ab : ∀ i ∈ ({1, 2, 3} : Finset ℕ),
  (∑ j ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α j) * Real.cos (β j)) = 0)
variable (h_bg : ∀ i ∈ ({1, 2, 3} : Finset ℕ),
  (∑ j ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β j) * Real.cos (γ j)) = 0)
variable (h_ga : ∀ i ∈ ({1, 2, 3} : Finset ℕ),
  (∑ j ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ j) * Real.cos (α j)) = 0)
variable (h_aa : ∀ i ∈ ({1, 2, 3} : Finset ℕ),
  (∑ j ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α j) ^ 2) = 1)
variable (h_bb : ∀ i ∈ ({1, 2, 3} : Finset ℕ),
  (∑ j ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β j) ^ 2) = 1)
variable (h_gg : ∀ i ∈ ({1, 2, 3} : Finset ℕ),
  (∑ j ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ j) ^ 2) = 1)

-- source gap 1
theorem proof_gap_exercise_3351_1 :
  dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    ∑ i ∈ ({1, 2, 3} : Finset ℕ),
      (FunDeri u 1 1 x y z * Real.cos (α i) +
        FunDeri u 2 1 x y z * Real.cos (β i) +
        FunDeri u 3 1 x y z * Real.cos (γ i)) ^ 2 := by
  sorry

-- source gap 2
theorem proof_gap_exercise_3351_2
  (h1 : dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    ∑ i ∈ ({1, 2, 3} : Finset ℕ),
      (FunDeri u 1 1 x y z * Real.cos (α i) +
        FunDeri u 2 1 x y z * Real.cos (β i) +
        FunDeri u 3 1 x y z * Real.cos (γ i)) ^ 2) :
  (∑ i ∈ ({1, 2, 3} : Finset ℕ),
      (FunDeri u 1 1 x y z * Real.cos (α i) +
        FunDeri u 2 1 x y z * Real.cos (β i) +
        FunDeri u 3 1 x y z * Real.cos (γ i)) ^ 2) =
    FunDeri u 1 1 x y z ^ 2 * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α i) ^ 2) +
    FunDeri u 2 1 x y z ^ 2 * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β i) ^ 2) +
    FunDeri u 3 1 x y z ^ 2 * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ i) ^ 2) +
    2 * FunDeri u 1 1 x y z * FunDeri u 2 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α i) * Real.cos (β i)) +
    2 * FunDeri u 2 1 x y z * FunDeri u 3 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β i) * Real.cos (γ i)) +
    2 * FunDeri u 3 1 x y z * FunDeri u 1 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ i) * Real.cos (α i)) := by
  sorry

-- source gap 3
theorem proof_gap_exercise_3351_3
  (h1 : dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    ∑ i ∈ ({1, 2, 3} : Finset ℕ),
      (FunDeri u 1 1 x y z * Real.cos (α i) +
        FunDeri u 2 1 x y z * Real.cos (β i) +
        FunDeri u 3 1 x y z * Real.cos (γ i)) ^ 2)
  (h2 : (∑ i ∈ ({1, 2, 3} : Finset ℕ),
      (FunDeri u 1 1 x y z * Real.cos (α i) +
        FunDeri u 2 1 x y z * Real.cos (β i) +
        FunDeri u 3 1 x y z * Real.cos (γ i)) ^ 2) =
    FunDeri u 1 1 x y z ^ 2 * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α i) ^ 2) +
    FunDeri u 2 1 x y z ^ 2 * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β i) ^ 2) +
    FunDeri u 3 1 x y z ^ 2 * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ i) ^ 2) +
    2 * FunDeri u 1 1 x y z * FunDeri u 2 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α i) * Real.cos (β i)) +
    2 * FunDeri u 2 1 x y z * FunDeri u 3 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β i) * Real.cos (γ i)) +
    2 * FunDeri u 3 1 x y z * FunDeri u 1 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ i) * Real.cos (α i))) :
  dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    FunDeri u 1 1 x y z ^ 2 + FunDeri u 2 1 x y z ^ 2 + FunDeri u 3 1 x y z ^ 2 := by
  sorry

-- source gap 4
theorem proof_gap_exercise_3351_4
  (h_part1 : dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    FunDeri u 1 1 x y z ^ 2 + FunDeri u 2 1 x y z ^ 2 + FunDeri u 3 1 x y z ^ 2) :
  (∑ i ∈ ({1, 2, 3} : Finset ℕ), dirDeri u l i 2 x y z) =
    FunDeri u 1 2 x y z * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α i) ^ 2) +
    FunDeri u 2 2 x y z * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β i) ^ 2) +
    FunDeri u 3 2 x y z * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ i) ^ 2) +
    2 * FunDeri (FunDeri u 1 1) 2 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α i) * Real.cos (β i)) +
    2 * FunDeri (FunDeri u 2 1) 3 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β i) * Real.cos (γ i)) +
    2 * FunDeri (FunDeri u 3 1) 1 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ i) * Real.cos (α i)) := by
  sorry

-- source gap 5
theorem proof_gap_exercise_3351_5
  (h_second_sum : (∑ i ∈ ({1, 2, 3} : Finset ℕ), dirDeri u l i 2 x y z) =
    FunDeri u 1 2 x y z * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α i) ^ 2) +
    FunDeri u 2 2 x y z * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β i) ^ 2) +
    FunDeri u 3 2 x y z * (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ i) ^ 2) +
    2 * FunDeri (FunDeri u 1 1) 2 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (α i) * Real.cos (β i)) +
    2 * FunDeri (FunDeri u 2 1) 3 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (β i) * Real.cos (γ i)) +
    2 * FunDeri (FunDeri u 3 1) 1 1 x y z *
      (∑ i ∈ ({1, 2, 3} : Finset ℕ), Real.cos (γ i) * Real.cos (α i))) :
  dirDeri u l 1 2 x y z + dirDeri u l 2 2 x y z + dirDeri u l 3 2 x y z =
    FunDeri u 1 2 x y z + FunDeri u 2 2 x y z + FunDeri u 3 2 x y z := by
  sorry

-- source gap 6
theorem proof_gap_exercise_3351_6
  (h_part1 : dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    FunDeri u 1 1 x y z ^ 2 + FunDeri u 2 1 x y z ^ 2 + FunDeri u 3 1 x y z ^ 2)
  (h_part2 : dirDeri u l 1 2 x y z + dirDeri u l 2 2 x y z + dirDeri u l 3 2 x y z =
    FunDeri u 1 2 x y z + FunDeri u 2 2 x y z + FunDeri u 3 2 x y z) :
  dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    FunDeri u 1 1 x y z ^ 2 + FunDeri u 2 1 x y z ^ 2 + FunDeri u 3 1 x y z ^ 2 := by
  sorry

-- source gap 7
theorem proof_gap_exercise_3351_7
  (h_part1 : dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    FunDeri u 1 1 x y z ^ 2 + FunDeri u 2 1 x y z ^ 2 + FunDeri u 3 1 x y z ^ 2)
  (h_part2 : dirDeri u l 1 2 x y z + dirDeri u l 2 2 x y z + dirDeri u l 3 2 x y z =
    FunDeri u 1 2 x y z + FunDeri u 2 2 x y z + FunDeri u 3 2 x y z) :
  dirDeri u l 1 2 x y z + dirDeri u l 2 2 x y z + dirDeri u l 3 2 x y z =
    FunDeri u 1 2 x y z + FunDeri u 2 2 x y z + FunDeri u 3 2 x y z := by
  sorry

-- source gap 8
theorem proof_gap_exercise_3351_8
  (h_part1 : dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    FunDeri u 1 1 x y z ^ 2 + FunDeri u 2 1 x y z ^ 2 + FunDeri u 3 1 x y z ^ 2)
  (h_part2 : dirDeri u l 1 2 x y z + dirDeri u l 2 2 x y z + dirDeri u l 3 2 x y z =
    FunDeri u 1 2 x y z + FunDeri u 2 2 x y z + FunDeri u 3 2 x y z) :
  (dirDeri u l 1 1 x y z ^ 2 + dirDeri u l 2 1 x y z ^ 2 + dirDeri u l 3 1 x y z ^ 2 =
    FunDeri u 1 1 x y z ^ 2 + FunDeri u 2 1 x y z ^ 2 + FunDeri u 3 1 x y z ^ 2) ∧
  (dirDeri u l 1 2 x y z + dirDeri u l 2 2 x y z + dirDeri u l 3 2 x y z =
    FunDeri u 1 2 x y z + FunDeri u 2 2 x y z + FunDeri u 3 2 x y z) := by
  sorry
