import Mathlib

-- Exercise 1087: derivatives and the differential on the punctured real domain.

/- Exercise 1087, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet ∧ a ≠ 0
3. x ∈ RealSet ∧ x ≠ -a ∧ x ≠ a
4. forall (x), x ∈ RealSet ∧ x ≠ -a ∧ x ≠ a ⇒ y(x) = frac(1, 2 * a) * ln(|frac(x - a, x + a)|)

GOAL:
FunDeri(y, 1, 1)(x) = frac(1, 2 * a) * (frac(1, x - a) - frac(1, x + a))

METHOD:

-/
theorem proof_gap_exercise_1087_1
  (y : ℝ → ℝ) (a x : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a ≠ 0)
  (hx : x ∈ (Set.univ : Set ℝ) ∧ x ≠ -a ∧ x ≠ a)
  (hy : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≠ -a ∧ t ≠ a →
    y t = 1 / (2 * a) * Real.log (|((t - a) / (t + a))|))
  : deriv y x = 1 / (2 * a) * (1 / (x - a) - 1 / (x + a)) := by
  sorry

/- Exercise 1087, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet ∧ a ≠ 0
3. x ∈ RealSet ∧ x ≠ -a ∧ x ≠ a
4. forall (x), x ∈ RealSet ∧ x ≠ -a ∧ x ≠ a ⇒ y(x) = frac(1, 2 * a) * ln(|frac(x - a, x + a)|)
5. FunDeri(y, 1, 1)(x) = frac(1, 2 * a) * (frac(1, x - a) - frac(1, x + a))

GOAL:
FunDeri(y, 1, 1)(x) = frac(1, x^{2} - a^{2})

METHOD:

-/
theorem proof_gap_exercise_1087_2
  (y : ℝ → ℝ) (a x : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a ≠ 0)
  (hx : x ∈ (Set.univ : Set ℝ) ∧ x ≠ -a ∧ x ≠ a)
  (hy : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≠ -a ∧ t ≠ a →
    y t = 1 / (2 * a) * Real.log (|((t - a) / (t + a))|))
  (h5 : deriv y x = 1 / (2 * a) * (1 / (x - a) - 1 / (x + a)))
  : deriv y x = 1 / (x ^ 2 - a ^ 2) := by
  sorry

/- Exercise 1087, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet ∧ a ≠ 0
3. x ∈ RealSet ∧ x ≠ -a ∧ x ≠ a
4. forall (x), x ∈ RealSet ∧ x ≠ -a ∧ x ≠ a ⇒ y(x) = frac(1, 2 * a) * ln(|frac(x - a, x + a)|)
5. FunDeri(y, 1, 1)(x) = frac(1, 2 * a) * (frac(1, x - a) - frac(1, x + a))
6. FunDeri(y, 1, 1)(x) = frac(1, x^{2} - a^{2})

GOAL:
diff(y) = (fun x [x ∈ RealSet ∧ x ≠ -a ∧ x ≠ a] . frac(1, x^{2} - a^{2})) * diff(fun x [x ∈ RealSet] . x)

METHOD:

-/
theorem proof_gap_exercise_1087_3
  (y : ℝ → ℝ) (a x : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a ≠ 0)
  (hx : x ∈ (Set.univ : Set ℝ) ∧ x ≠ -a ∧ x ≠ a)
  (hy : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≠ -a ∧ t ≠ a →
    y t = 1 / (2 * a) * Real.log (|((t - a) / (t + a))|))
  (h5 : deriv y x = 1 / (2 * a) * (1 / (x - a) - 1 / (x + a)))
  (h6 : deriv y x = 1 / (x ^ 2 - a ^ 2))
  -- Equality of differential fields restricted to the source coefficient's domain.
  : (fun t : {t : ℝ // t ≠ -a ∧ t ≠ a} => fderiv ℝ y t.val) =
    (fun t : {t : ℝ // t ≠ -a ∧ t ≠ a} =>
      (1 / (t.val ^ 2 - a ^ 2)) • fderiv ℝ (fun u : ℝ => u) t.val) := by
  sorry
