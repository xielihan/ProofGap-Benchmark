import Mathlib

-- exercise: exercise_1174
-- A fourth differential is the homogeneous map h ↦ f⁽⁴⁾(x) * h^4.
-- All differential sections below have the source domain x > 0.
namespace Exercise1174

abbrev PositiveReal := {x : ℝ // 0 < x}

noncomputable def fourthDifferential (f : ℝ → ℝ) (x : PositiveReal) : ℝ → ℝ :=
  fun h => iteratedDerivWithin 4 f (Set.Ioi 0) x.val * h ^ 4

noncomputable def dx (x h : ℝ) : ℝ := deriv (fun t : ℝ => t) x * h

/- Exercise 1174, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ x > 0 ⇒ y(x) = e^{x} * ln(x)

GOAL:
forall (x), x ∈ RealSet ∧ x > 0 ⇒ diff^{4}(y) = FunDeri(fun x [x ∈ RealSet ∧ x > 0] . e^{x} * ln(x), 1, 4)(x) * diff(fun x [x ∈ RealSet] . x)^{4}

METHOD:

-/
theorem proof_gap_exercise_1174_1
    (y : ℝ → ℝ)
    (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 →
      y x = Real.exp x * Real.log x)
    : ∀ (x : ℝ) (hx : x ∈ (Set.univ : Set ℝ) ∧ x > 0),
      fourthDifferential y ⟨x, hx.2⟩ =
        (fun h : ℝ => iteratedDerivWithin 4
          (fun t : ℝ => Real.exp t * Real.log t) (Set.Ioi 0) x * (dx x h) ^ 4) := by
  sorry

/- Exercise 1174, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ x > 0 ⇒ y(x) = e^{x} * ln(x)
3. forall (x), x ∈ RealSet ∧ x > 0 ⇒ diff^{4}(y) = FunDeri(fun x [x ∈ RealSet ∧ x > 0] . e^{x} * ln(x), 1, 4)(x) * diff(fun x [x ∈ RealSet] . x)^{4}

GOAL:
diff^{4}(y) = (fun x [x ∈ RealSet ∧ x > 0] . e^{x} * (ln(x) + frac(4, x) - frac(6, x^{2}) + frac(8, x^{3}) - frac(6, x^{4}))) * diff(fun x [x ∈ RealSet] . x)^{4}

METHOD:

-/
theorem proof_gap_exercise_1174_2
    (y : ℝ → ℝ)
    (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 →
      y x = Real.exp x * Real.log x)
    (hprevious : ∀ (x : ℝ) (hx : x ∈ (Set.univ : Set ℝ) ∧ x > 0),
      fourthDifferential y ⟨x, hx.2⟩ =
        (fun h : ℝ => iteratedDerivWithin 4
          (fun t : ℝ => Real.exp t * Real.log t) (Set.Ioi 0) x * (dx x h) ^ 4))
    : fourthDifferential y =
        (fun (x : PositiveReal) (h : ℝ) =>
          Real.exp x.val * (Real.log x.val + 4 / x.val - 6 / x.val ^ 2 +
            8 / x.val ^ 3 - 6 / x.val ^ 4) * (dx x.val h) ^ 4) := by
  sorry

end Exercise1174
