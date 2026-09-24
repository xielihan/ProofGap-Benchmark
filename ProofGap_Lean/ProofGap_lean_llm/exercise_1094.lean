import Mathlib

/- The differential df at x applied to a real increment dx is f′(x) * dx.
The restricted coefficient functions have domain I; identities are on I.
DiffableFuncOn means ordinary differentiability at every point of I,
as specified by the theorem library, theorems 276 and 277.
The source does not assume I open: see the source issue in the review. -/
namespace Exercise1094

noncomputable def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

end Exercise1094

/- Exercise 1094, gap 1
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
9. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ v(x) ≠ 0 ∧ y(x) = arctan(frac(u(x), v(x)))

GOAL:
diff(y) = (fun x [x ∈ RealSet ∧ x ∈ I] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(u) - (fun x [x ∈ RealSet ∧ x ∈ I] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(v)

METHOD:

-/
theorem proof_gap_exercise_1094_1
    (I : Set ℝ) (u v y : ℝ → ℝ)
    (h1 : I ⊆ (Set.univ : Set ℝ))
    (h5 : Set.MapsTo u I Set.univ)
    (h6 : Set.MapsTo v I Set.univ)
    (h7 : ∀ x ∈ I, DifferentiableAt ℝ u x)
    (h8 : ∀ x ∈ I, DifferentiableAt ℝ v x)
    (h9 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ I →
      v x ≠ 0 ∧ y x = Real.arctan (u x / v x))
    : (∀ x : ℝ, x ∈ Set.univ ∧ x ∈ I → ∀ dx : ℝ,
      Exercise1094.differential y x dx =
        (v x / (u x ^ 2 + v x ^ 2)) * Exercise1094.differential u x dx -
        (u x / (u x ^ 2 + v x ^ 2)) * Exercise1094.differential v x dx) := by
  sorry

/- Exercise 1094, gap 2
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
9. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ v(x) ≠ 0 ∧ y(x) = arctan(frac(u(x), v(x)))
10. diff(y) = (fun x [x ∈ RealSet ∧ x ∈ I] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(u) - (fun x [x ∈ RealSet ∧ x ∈ I] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(v)

GOAL:
diff(y) = (fun x [x ∈ RealSet ∧ x ∈ I] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(u) - (fun x [x ∈ RealSet ∧ x ∈ I] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(v)

METHOD:

-/
theorem proof_gap_exercise_1094_2
    (I : Set ℝ) (u v y : ℝ → ℝ)
    (h1 : I ⊆ (Set.univ : Set ℝ))
    (h5 : Set.MapsTo u I Set.univ)
    (h6 : Set.MapsTo v I Set.univ)
    (h7 : ∀ x ∈ I, DifferentiableAt ℝ u x)
    (h8 : ∀ x ∈ I, DifferentiableAt ℝ v x)
    (h9 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ I →
      v x ≠ 0 ∧ y x = Real.arctan (u x / v x))
    (h10 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ I → ∀ dx : ℝ,
      Exercise1094.differential y x dx =
        (v x / (u x ^ 2 + v x ^ 2)) * Exercise1094.differential u x dx -
        (u x / (u x ^ 2 + v x ^ 2)) * Exercise1094.differential v x dx)
    : (∀ x : ℝ, x ∈ Set.univ ∧ x ∈ I → ∀ dx : ℝ,
      Exercise1094.differential y x dx =
        (v x / (u x ^ 2 + v x ^ 2)) * Exercise1094.differential u x dx -
        (u x / (u x ^ 2 + v x ^ 2)) * Exercise1094.differential v x dx) := by
  sorry

