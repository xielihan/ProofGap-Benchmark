import Mathlib

set_option linter.style.longLine false

open scoped BigOperators

abbrev Point3 := ℝ × ℝ × ℝ

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def diff1 (_ : ℝ → ℝ) : ℝ := 1
noncomputable def diff3 (_ : ℝ → ℝ → ℝ → ℝ) : ℝ := 1
noncomputable def VectorCurveInt (_C : Set Point3) (integrand : ℝ) : ℝ := integrand
noncomputable def VectorSurfaceInt (_S : Set Point3) (integrand : ℝ) : ℝ := integrand
noncomputable def DefInt (_a _b : ℝ) (integrand : ℝ) : ℝ := integrand

noncomputable def curve4374 (a : ℝ) : Set Point3 :=
  {p | ∃ t : ℝ,
    0 ≤ t ∧ t ≤ 2 * Real.pi ∧
      p.1 = a * Real.cos t ∧
      p.2.1 = a * Real.cos (2 * t) ∧
      p.2.2 = a * Real.cos (3 * t)}

noncomputable def surface4374 (a : ℝ) : Set Point3 :=
  {p | ∃ u t : ℝ,
    0 ≤ u ∧ u ≤ a ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi ∧
      p.1 = u * Real.cos t ∧
      p.2.1 = u * Real.cos (2 * t) ∧
      p.2.2 = u * Real.cos (3 * t)}

noncomputable def trigIntegrand4374 (t : ℝ) : ℝ :=
  Real.cos t ^ (2 : ℕ) * (Real.cos (2 * t) - Real.cos (3 * t)) *
      (2 * Real.sin (2 * t) * Real.cos (3 * t) - 3 * Real.cos (2 * t) * Real.sin (3 * t)) +
    Real.cos (2 * t) ^ (2 : ℕ) * (Real.cos (3 * t) - Real.cos t) *
      (3 * Real.sin (3 * t) * Real.cos t - Real.sin t * Real.cos (3 * t)) +
    Real.cos (3 * t) ^ (2 : ℕ) * (Real.cos t - Real.cos (2 * t)) *
      (Real.sin t * Real.cos (2 * t) - 2 * Real.sin (2 * t) * Real.cos t)

-- exercise: exercise_4374

-- gap 1: the boundary curve is represented by the u=a edge of the parametrized surface.
theorem proof_gap_exercise_4374_1
  (C S : Set Point3)
  (a x y z u t : ℝ)
  (h1 : C ⊆ (Set.univ : Set Point3))
  (h2 : S ⊆ (Set.univ : Set Point3))
  (ha : 0 < a)
  (hC : C = curve4374 a)
  (hS : S = surface4374 a) :
  C = {p : Point3 | p ∈ S ∧ u = a} := by
  sorry

-- gap 2: Stokes formula converts the line integral to the curl flux.
theorem proof_gap_exercise_4374_2
  (C S : Set Point3)
  (a x y z u t : ℝ)
  (h1 : C ⊆ (Set.univ : Set Point3))
  (h2 : S ⊆ (Set.univ : Set Point3))
  (ha : 0 < a)
  (hC : C = curve4374 a)
  (hS : S = surface4374 a)
  (hboundary : C = {p : Point3 | p ∈ S ∧ u = a}) :
  VectorCurveInt C
      (y ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun x _y _z => x) +
       x ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun _x y _z => y) +
       x ^ (2 : ℕ) * y ^ (2 : ℕ) * diff3 (fun _x _y z => z)) =
    2 * VectorSurfaceInt S
      (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
       y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
       z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) := by
  sorry

-- gap 3: substitute the surface parametrization and separate the u and t factors.
theorem proof_gap_exercise_4374_3
  (C S : Set Point3)
  (a x y z u t : ℝ)
  (h1 : C ⊆ (Set.univ : Set Point3))
  (h2 : S ⊆ (Set.univ : Set Point3))
  (ha : 0 < a)
  (hC : C = curve4374 a)
  (hS : S = surface4374 a)
  (hboundary : C = {p : Point3 | p ∈ S ∧ u = a})
  (hstokes :
    VectorCurveInt C
        (y ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun x _y _z => x) +
         x ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun _x y _z => y) +
         x ^ (2 : ℕ) * y ^ (2 : ℕ) * diff3 (fun _x _y z => z)) =
      2 * VectorSurfaceInt S
        (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y))) :
  VectorSurfaceInt S
      (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
       y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
       z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
    DefInt 0 a (u ^ (4 : ℕ) * diff1 (fun u => u)) *
      DefInt 0 (2 * Real.pi) (trigIntegrand4374 t * diff1 (fun t => t)) := by
  sorry

-- gap 4: evaluate the u integral and replace the periodic t interval by [-pi,pi].
theorem proof_gap_exercise_4374_4
  (C S : Set Point3)
  (a x y z u t : ℝ)
  (h1 : C ⊆ (Set.univ : Set Point3))
  (h2 : S ⊆ (Set.univ : Set Point3))
  (ha : 0 < a)
  (hC : C = curve4374 a)
  (hS : S = surface4374 a)
  (hboundary : C = {p : Point3 | p ∈ S ∧ u = a})
  (hstokes :
    VectorCurveInt C
        (y ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun x _y _z => x) +
         x ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun _x y _z => y) +
         x ^ (2 : ℕ) * y ^ (2 : ℕ) * diff3 (fun _x _y z => z)) =
      2 * VectorSurfaceInt S
        (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)))
  (hparam :
    VectorSurfaceInt S
        (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
      DefInt 0 a (u ^ (4 : ℕ) * diff1 (fun u => u)) *
        DefInt 0 (2 * Real.pi) (trigIntegrand4374 t * diff1 (fun t => t))) :
  2 * DefInt 0 a (u ^ (4 : ℕ) * diff1 (fun u => u)) *
      DefInt 0 (2 * Real.pi) (trigIntegrand4374 t * diff1 (fun t => t)) =
    (2 /. 5) * a ^ (5 : ℕ) *
      DefInt (-Real.pi) Real.pi (trigIntegrand4374 t * diff1 (fun t => t)) := by
  sorry

-- gap 5: the t-integrand is odd on [-pi,pi], hence its integral is zero.
theorem proof_gap_exercise_4374_5
  (C S : Set Point3)
  (a x y z u t : ℝ)
  (h1 : C ⊆ (Set.univ : Set Point3))
  (h2 : S ⊆ (Set.univ : Set Point3))
  (ha : 0 < a)
  (hC : C = curve4374 a)
  (hS : S = surface4374 a)
  (hboundary : C = {p : Point3 | p ∈ S ∧ u = a})
  (hstokes :
    VectorCurveInt C
        (y ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun x _y _z => x) +
         x ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun _x y _z => y) +
         x ^ (2 : ℕ) * y ^ (2 : ℕ) * diff3 (fun _x _y z => z)) =
      2 * VectorSurfaceInt S
        (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)))
  (hparam :
    VectorSurfaceInt S
        (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
      DefInt 0 a (u ^ (4 : ℕ) * diff1 (fun u => u)) *
        DefInt 0 (2 * Real.pi) (trigIntegrand4374 t * diff1 (fun t => t)))
  (hreduce :
    2 * DefInt 0 a (u ^ (4 : ℕ) * diff1 (fun u => u)) *
        DefInt 0 (2 * Real.pi) (trigIntegrand4374 t * diff1 (fun t => t)) =
      (2 /. 5) * a ^ (5 : ℕ) *
        DefInt (-Real.pi) Real.pi (trigIntegrand4374 t * diff1 (fun t => t))) :
  DefInt (-Real.pi) Real.pi (trigIntegrand4374 t * diff1 (fun t => t)) = 0 := by
  sorry

-- gap 6: combine the previous equalities to obtain the original line integral value.
theorem proof_gap_exercise_4374_6
  (C S : Set Point3)
  (a x y z u t : ℝ)
  (h1 : C ⊆ (Set.univ : Set Point3))
  (h2 : S ⊆ (Set.univ : Set Point3))
  (ha : 0 < a)
  (hC : C = curve4374 a)
  (hS : S = surface4374 a)
  (hboundary : C = {p : Point3 | p ∈ S ∧ u = a})
  (hstokes :
    VectorCurveInt C
        (y ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun x _y _z => x) +
         x ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun _x y _z => y) +
         x ^ (2 : ℕ) * y ^ (2 : ℕ) * diff3 (fun _x _y z => z)) =
      2 * VectorSurfaceInt S
        (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)))
  (hparam :
    VectorSurfaceInt S
        (x ^ (2 : ℕ) * (y - z) * diff3 (fun _x y _z => y) * diff3 (fun _x _y z => z) +
         y ^ (2 : ℕ) * (z - x) * diff3 (fun _x _y z => z) * diff3 (fun x _y _z => x) +
         z ^ (2 : ℕ) * (x - y) * diff3 (fun x _y _z => x) * diff3 (fun _x y _z => y)) =
      DefInt 0 a (u ^ (4 : ℕ) * diff1 (fun u => u)) *
        DefInt 0 (2 * Real.pi) (trigIntegrand4374 t * diff1 (fun t => t)))
  (hreduce :
    2 * DefInt 0 a (u ^ (4 : ℕ) * diff1 (fun u => u)) *
        DefInt 0 (2 * Real.pi) (trigIntegrand4374 t * diff1 (fun t => t)) =
      (2 /. 5) * a ^ (5 : ℕ) *
        DefInt (-Real.pi) Real.pi (trigIntegrand4374 t * diff1 (fun t => t)))
  (hodd : DefInt (-Real.pi) Real.pi (trigIntegrand4374 t * diff1 (fun t => t)) = 0) :
  VectorCurveInt C
      (y ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun x _y _z => x) +
       x ^ (2 : ℕ) * z ^ (2 : ℕ) * diff3 (fun _x y _z => y) +
       x ^ (2 : ℕ) * y ^ (2 : ℕ) * diff3 (fun _x _y z => z)) = 0 := by
  sorry
