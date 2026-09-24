import Mathlib

-- Differentials at x, evaluated on arbitrary first and second increments.
-- For a twice differentiable intermediate variable x(t), these increments
-- are x'(t) dt and x''(t) dt^2. In particular d^2(id) is not set to zero.
namespace Exercise1130_2

noncomputable def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

noncomputable def secondDifferential (f : ℝ → ℝ) (x dx ddx : ℝ) : ℝ :=
  deriv (deriv f) x * dx ^ 2 + deriv f x * ddx

end Exercise1130_2

open Exercise1130_2

-- Exercise 1130_2, gap 1
/-
PROOF GAP @1
ASSUM:
1. x ∈ RealSet
2. y : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = e^{x}

GOAL:
diff(y) = e^{x} * diff(fun x [x ∈ RealSet] . x)

METHOD:

-/
theorem proof_gap_exercise_1130_2_1
    (x : ℝ) (y : ℝ → ℝ)
    (h1 : x ∈ (Set.univ : Set ℝ))
    (h3 : ∀ z : ℝ, z ∈ (Set.univ : Set ℝ) → y z = Real.exp z)
    : ∀ dx : ℝ,
      differential y x dx = Real.exp x * differential (fun z : ℝ => z) x dx := by
  sorry

-- Exercise 1130_2, gap 2
/-
PROOF GAP @2
ASSUM:
1. x ∈ RealSet
2. y : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = e^{x}
4. diff(y) = e^{x} * diff(fun x [x ∈ RealSet] . x)

GOAL:
diff^{2}(y) = e^{x} * diff^{2}(fun x [x ∈ RealSet] . x) + e^{x} * diff(fun x [x ∈ RealSet] . x)^{2}

METHOD:

-/
theorem proof_gap_exercise_1130_2_2
    (x : ℝ) (y : ℝ → ℝ)
    (h1 : x ∈ (Set.univ : Set ℝ))
    (h3 : ∀ z : ℝ, z ∈ (Set.univ : Set ℝ) → y z = Real.exp z)
    (h4 : ∀ dx : ℝ,
      differential y x dx = Real.exp x * differential (fun z : ℝ => z) x dx)
    : ∀ dx ddx : ℝ,
      secondDifferential y x dx ddx =
        Real.exp x * secondDifferential (fun z : ℝ => z) x dx ddx +
        Real.exp x * (differential (fun z : ℝ => z) x dx) ^ 2 := by
  sorry
