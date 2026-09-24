import Mathlib

-- exercise: exercise_1134_2
-- Formal differentials in the independent real coordinate, with a common increment dx.
-- The unqualified source equalities are global; no x ∈ I restriction is added.
-- See the review for the resulting source domain issue.
namespace Exercise1134_2

noncomputable def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

noncomputable def secondDifferential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  iteratedDeriv 2 f x * dx^2

end Exercise1134_2

open Exercise1134_2

/- Exercise 1134_2, gap 1
SHA-256: bf1ed7f9520a6851c87c0a1f82b6085962edcb7ff961b6f4603f42ffc37513f5
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. I ⊆ RealSet
5. FuncOfClassKOn(u, I, 2)
6. FuncOfClassKOn(v, I, 2)
7. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ v(x) ≠ 0
8. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = frac(u(x), v(x))

GOAL:
diff(y) = frac(v * diff(u) - u * diff(v), v^{2})

METHOD:

-/
theorem proof_gap_exercise_1134_2_1
  (y u v : ℝ → ℝ) (I : Set ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u I)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v I)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → v x ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x / v x)
  : ∀ x dx : ℝ, differential y x dx =
    (v x * differential u x dx - u x * differential v x dx) / (v x)^2 := by
  sorry

/- Exercise 1134_2, gap 2
SHA-256: 88c5c7a008e99efea61d69e01f76b7bfd4c326e2824d341de1e69b3b8b0ce6c3
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. I ⊆ RealSet
5. FuncOfClassKOn(u, I, 2)
6. FuncOfClassKOn(v, I, 2)
7. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ v(x) ≠ 0
8. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = frac(u(x), v(x))
9. diff(y) = frac(v * diff(u) - u * diff(v), v^{2})

GOAL:
diff^{2}(y) = frac(v^{2} * (diff(v) * diff(u) + v * diff^{2}(u) - diff(u) * diff(v) - u * diff^{2}(v)) - 2 * v * diff(v) * (v * diff(u) - u * diff(v)), v^{4})

METHOD:

-/
theorem proof_gap_exercise_1134_2_2
  (y u v : ℝ → ℝ) (I : Set ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u I)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v I)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → v x ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x / v x)
  (h6 : ∀ x dx : ℝ, differential y x dx =
    (v x * differential u x dx - u x * differential v x dx) / (v x)^2)
  : ∀ x dx : ℝ, secondDifferential y x dx =
    ((v x)^2 * (differential v x dx * differential u x dx +
      v x * secondDifferential u x dx - differential u x dx * differential v x dx -
      u x * secondDifferential v x dx) -
      2 * v x * differential v x dx *
        (v x * differential u x dx - u x * differential v x dx)) / (v x)^4 := by
  sorry

/- Exercise 1134_2, gap 3
SHA-256: 9446e01acc0d8f6f2c9e1d89edabf28b2b05a63d5ff5e8d53763479609bd7582
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. I ⊆ RealSet
5. FuncOfClassKOn(u, I, 2)
6. FuncOfClassKOn(v, I, 2)
7. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ v(x) ≠ 0
8. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = frac(u(x), v(x))
9. diff(y) = frac(v * diff(u) - u * diff(v), v^{2})
10. diff^{2}(y) = frac(v^{2} * (diff(v) * diff(u) + v * diff^{2}(u) - diff(u) * diff(v) - u * diff^{2}(v)) - 2 * v * diff(v) * (v * diff(u) - u * diff(v)), v^{4})

GOAL:
diff^{2}(y) = frac(v * (v * diff^{2}(u) - u * diff^{2}(v)) - 2 * diff(v) * (v * diff(u) - u * diff(v)), v^{3})

METHOD:

-/
theorem proof_gap_exercise_1134_2_3
  (y u v : ℝ → ℝ) (I : Set ℝ)
  (h1 : I ⊆ (Set.univ : Set ℝ))
  (h2 : ContDiffOn ℝ (2 : ℕ∞) u I)
  (h3 : ContDiffOn ℝ (2 : ℕ∞) v I)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → v x ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x / v x)
  (h6 : ∀ x dx : ℝ, differential y x dx =
    (v x * differential u x dx - u x * differential v x dx) / (v x)^2)
  (h7 : ∀ x dx : ℝ, secondDifferential y x dx =
    ((v x)^2 * (differential v x dx * differential u x dx +
      v x * secondDifferential u x dx - differential u x dx * differential v x dx -
      u x * secondDifferential v x dx) -
      2 * v x * differential v x dx *
        (v x * differential u x dx - u x * differential v x dx)) / (v x)^4)
  : ∀ x dx : ℝ, secondDifferential y x dx =
    (v x * (v x * secondDifferential u x dx - u x * secondDifferential v x dx) -
      2 * differential v x dx *
        (v x * differential u x dx - u x * differential v x dx)) / (v x)^3 := by
  sorry

