import Mathlib

set_option linter.style.longLine false

open scoped BigOperators

abbrev Point3 := ℝ × ℝ × ℝ

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def diff3 (_ : ℝ → ℝ → ℝ → ℝ) : ℝ := 1
noncomputable def VectorSurfaceInt (_S : Set Point3) (integrand : ℝ) : ℝ := integrand
noncomputable def VolumeInt (_V : Set Point3) (integrand : ℝ) : ℝ := integrand
noncomputable def FunDeri (F : ℝ → ℝ → ℝ → ℝ) (_coord order : ℕ) : ℝ → ℝ → ℝ → ℝ := F

-- exercise: exercise_4376

-- gap 1: compute div(x^3,y^3,z^3)=3*(x^2+y^2+z^2).
theorem proof_gap_exercise_4376_1
  (S V : Set Point3)
  (P Q R : ℝ → ℝ → ℝ → ℝ)
  (x y z : ℝ)
  (h1 : S ⊆ (Set.univ : Set Point3))
  (h2 : V ⊆ (Set.univ : Set Point3))
  (h3 : P = fun x _y _z => x ^ (3 : ℕ))
  (h4 : Q = fun _x y _z => y ^ (3 : ℕ))
  (h5 : R = fun _x _y z => z ^ (3 : ℕ)) :
  FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z =
    3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)) := by
  sorry

-- gap 2: apply Gauss formula to the outward closed surface.
theorem proof_gap_exercise_4376_2
  (S V : Set Point3)
  (P Q R : ℝ → ℝ → ℝ → ℝ)
  (x y z : ℝ)
  (h1 : S ⊆ (Set.univ : Set Point3))
  (h2 : V ⊆ (Set.univ : Set Point3))
  (h3 : P = fun x _y _z => x ^ (3 : ℕ))
  (h4 : Q = fun _x y _z => y ^ (3 : ℕ))
  (h5 : R = fun _x _y z => z ^ (3 : ℕ))
  (h6 :
    FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z =
      3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ))) :
  VectorSurfaceInt S
      (x ^ (3 : ℕ) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
       y ^ (3 : ℕ) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
       z ^ (3 : ℕ) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
    VolumeInt V
      ((FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z) *
       diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z)) := by
  sorry

-- gap 3: substitute the divergence value into the volume integral.
theorem proof_gap_exercise_4376_3
  (S V : Set Point3)
  (P Q R : ℝ → ℝ → ℝ → ℝ)
  (x y z : ℝ)
  (h1 : S ⊆ (Set.univ : Set Point3))
  (h2 : V ⊆ (Set.univ : Set Point3))
  (h3 : P = fun x _y _z => x ^ (3 : ℕ))
  (h4 : Q = fun _x y _z => y ^ (3 : ℕ))
  (h5 : R = fun _x _y z => z ^ (3 : ℕ))
  (h6 :
    FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z =
      3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h7 :
    VectorSurfaceInt S
        (x ^ (3 : ℕ) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (3 : ℕ) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (3 : ℕ) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
      VolumeInt V
        ((FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z) *
         diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z))) :
  VolumeInt V
      ((FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z) *
       diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z)) =
    3 * VolumeInt V
      ((x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)) *
       diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z)) := by
  sorry

-- gap 4: combine Gauss formula and substitution.
theorem proof_gap_exercise_4376_4
  (S V : Set Point3)
  (P Q R : ℝ → ℝ → ℝ → ℝ)
  (x y z : ℝ)
  (h1 : S ⊆ (Set.univ : Set Point3))
  (h2 : V ⊆ (Set.univ : Set Point3))
  (h3 : P = fun x _y _z => x ^ (3 : ℕ))
  (h4 : Q = fun _x y _z => y ^ (3 : ℕ))
  (h5 : R = fun _x _y z => z ^ (3 : ℕ))
  (h6 :
    FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z =
      3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h7 :
    VectorSurfaceInt S
        (x ^ (3 : ℕ) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (3 : ℕ) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (3 : ℕ) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
      VolumeInt V
        ((FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z) *
         diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z)))
  (h8 :
    VolumeInt V
        ((FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z) *
         diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z)) =
      3 * VolumeInt V
        ((x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)) *
         diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z))) :
  VectorSurfaceInt S
      (x ^ (3 : ℕ) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
       y ^ (3 : ℕ) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
       z ^ (3 : ℕ) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
    3 * VolumeInt V
      ((x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)) *
       diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z)) := by
  sorry
