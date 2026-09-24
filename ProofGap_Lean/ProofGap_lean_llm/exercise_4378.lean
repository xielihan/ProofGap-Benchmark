import Mathlib

set_option linter.style.longLine false

open scoped BigOperators

abbrev Point3 := ℝ × ℝ × ℝ

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def diff3 (_ : ℝ → ℝ → ℝ → ℝ) : ℝ := 1
noncomputable def VectorSurfaceInt (_S : Set Point3) (integrand : ℝ) : ℝ := integrand
noncomputable def VolumeInt (_V : Set Point3) (integrand : ℝ) : ℝ := integrand
noncomputable def FunDeri (F : ℝ → ℝ → ℝ → ℝ) (_coord order : ℕ) : ℝ → ℝ → ℝ → ℝ := F

-- exercise: exercise_4378

-- gap 1: compute the divergence of the radial unit field away from the origin.
theorem proof_gap_exercise_4378_1
  (S V : Set Point3)
  (P Q R : ℝ → ℝ → ℝ → ℝ)
  (h1 : S ⊆ (Set.univ : Set Point3))
  (h2 : V ⊆ (Set.univ : Set Point3))
  (h3 : ∀ x y z : ℝ, P x y z = x /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h4 : ∀ x y z : ℝ, Q x y z = y /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h5 : ∀ x y z : ℝ, R x y z = z /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h6 :
    ∀ x y z : ℝ,
      ((x, y, z) ∈ V ∪ S) → x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ) > 0) :
  ∀ x y z : ℝ,
    FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z =
      2 /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)) := by
  sorry

-- gap 2: apply Gauss formula to the radial field.
theorem proof_gap_exercise_4378_2
  (S V : Set Point3)
  (P Q R : ℝ → ℝ → ℝ → ℝ)
  (h1 : S ⊆ (Set.univ : Set Point3))
  (h2 : V ⊆ (Set.univ : Set Point3))
  (h3 : ∀ x y z : ℝ, P x y z = x /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h4 : ∀ x y z : ℝ, Q x y z = y /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h5 : ∀ x y z : ℝ, R x y z = z /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h6 :
    ∀ x y z : ℝ,
      ((x, y, z) ∈ V ∪ S) → x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ) > 0)
  (h7 :
    ∀ x y z : ℝ,
      FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z =
        2 /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ))) :
  ∀ x y z : ℝ,
    VectorSurfaceInt S
        (P x y z * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         Q x y z * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         R x y z * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
      VolumeInt V
        ((2 /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ))) *
         diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z)) := by
  sorry

-- gap 3: factor the scalar 2 out of the volume integral.
theorem proof_gap_exercise_4378_3
  (S V : Set Point3)
  (P Q R : ℝ → ℝ → ℝ → ℝ)
  (h1 : S ⊆ (Set.univ : Set Point3))
  (h2 : V ⊆ (Set.univ : Set Point3))
  (h3 : ∀ x y z : ℝ, P x y z = x /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h4 : ∀ x y z : ℝ, Q x y z = y /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h5 : ∀ x y z : ℝ, R x y z = z /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h6 :
    ∀ x y z : ℝ,
      ((x, y, z) ∈ V ∪ S) → x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ) > 0)
  (h7 :
    ∀ x y z : ℝ,
      FunDeri P 1 1 x y z + FunDeri Q 2 1 x y z + FunDeri R 3 1 x y z =
        2 /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)))
  (h8 :
    ∀ x y z : ℝ,
      VectorSurfaceInt S
          (P x y z * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
           Q x y z * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
           R x y z * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
        VolumeInt V
          ((2 /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ))) *
           diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z))) :
  ∀ x y z : ℝ,
    VectorSurfaceInt S
        (P x y z * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         Q x y z * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         R x y z * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
      2 * VolumeInt V
        ((1 /. Real.sqrt (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ))) *
         diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z)) := by
  sorry
