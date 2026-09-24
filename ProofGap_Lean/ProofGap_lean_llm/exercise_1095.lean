import Mathlib

-- Differentials are continuous linear maps, restricted to the coefficient domain I.
-- Differentiability on I means ordinary differentiability at every point of I.

/- Exercise 1095, gap 1
PROOF GAP @1
ASSUM:
1. I ⊆ RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. y : RealSet → RealSet
5. u : I → RealSet
6. v : I → RealSet
7. DiffableFuncOn(u, I)
8. DiffableFuncOn(v, I)
9. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = ln(sqrtn(2, u(x)^{2} + v(x)^{2}))
10. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ u(x)^{2} + v(x)^{2} > 0
11. I = RealSet
GOAL:
diff(y) = (fun x [x ∈ RealSet ∧ x ∈ I] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(u) + (fun x [x ∈ RealSet ∧ x ∈ I] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(v)

METHOD:

-/
theorem proof_gap_exercise_1095_1
  (I : Set ℝ) (u v y : ℝ → ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h5 : Set.MapsTo u I (Set.univ : Set ℝ))
  (h6 : Set.MapsTo v I (Set.univ : Set ℝ))
  (h7 : ∀ x ∈ I, DifferentiableAt ℝ u x)
  (h8 : ∀ x ∈ I, DifferentiableAt ℝ v x)
  (h9 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I →
    y x = Real.log (Real.sqrt (u x ^ 2 + v x ^ 2)))
  (h10 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I →
    u x ^ 2 + v x ^ 2 > 0)
  (h11 : I = (Set.univ : Set ℝ))
  : (fun x : I => fderiv ℝ y (x : ℝ)) =
      (fun x : I =>
        (u x / (u x ^ 2 + v x ^ 2)) • fderiv ℝ u (x : ℝ) +
        (v x / (u x ^ 2 + v x ^ 2)) • fderiv ℝ v (x : ℝ)) := by
  sorry

/- Exercise 1095, gap 2
PROOF GAP @2
ASSUM:
1. I ⊆ RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. y : RealSet → RealSet
5. u : I → RealSet
6. v : I → RealSet
7. DiffableFuncOn(u, I)
8. DiffableFuncOn(v, I)
9. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = ln(sqrtn(2, u(x)^{2} + v(x)^{2}))
10. diff(y) = (fun x [x ∈ RealSet ∧ x ∈ I] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(u) + (fun x [x ∈ RealSet ∧ x ∈ I] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(v)

GOAL:
diff(y) = (fun x [x ∈ RealSet ∧ x ∈ I] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(u) + (fun x [x ∈ RealSet ∧ x ∈ I] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(v)

METHOD:

-/
theorem proof_gap_exercise_1095_2
  (I : Set ℝ) (u v y : ℝ → ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h5 : Set.MapsTo u I (Set.univ : Set ℝ))
  (h6 : Set.MapsTo v I (Set.univ : Set ℝ))
  (h7 : ∀ x ∈ I, DifferentiableAt ℝ u x)
  (h8 : ∀ x ∈ I, DifferentiableAt ℝ v x)
  (h9 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I →
    y x = Real.log (Real.sqrt (u x ^ 2 + v x ^ 2)))
  (h10 : (fun x : I => fderiv ℝ y (x : ℝ)) =
      (fun x : I =>
        (u x / (u x ^ 2 + v x ^ 2)) • fderiv ℝ u (x : ℝ) +
        (v x / (u x ^ 2 + v x ^ 2)) • fderiv ℝ v (x : ℝ)))
  : (fun x : I => fderiv ℝ y (x : ℝ)) =
      (fun x : I =>
        (u x / (u x ^ 2 + v x ^ 2)) • fderiv ℝ u (x : ℝ) +
        (v x / (u x ^ 2 + v x ^ 2)) • fderiv ℝ v (x : ℝ)) := by
  sorry

