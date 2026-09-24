import Mathlib

-- exercise: exercise_1088
-- Differentials are continuous linear maps, compared on the source coefficient domain.

/- Exercise 1088, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet ∧ x^{2} + a > 0 ∧ x + sqrtn(2, x^{2} + a) ≠ 0
4. forall (x), x ∈ RealSet ∧ x^{2} + a > 0 ∧ x + sqrtn(2, x^{2} + a) ≠ 0 ⇒ y(x) = ln(|x + sqrtn(2, x^{2} + a)|)

GOAL:
FunDeri(y, 1, 1)(x) = frac(1, sqrtn(2, x^{2} + a))

METHOD:

-/
theorem proof_gap_exercise_1088_1
  (y : ℝ → ℝ) (a x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ) ∧ 0 < x ^ 2 + a ∧
    x + Real.sqrt (x ^ 2 + a) ≠ 0)
  (h3 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 < t ^ 2 + a ∧
    t + Real.sqrt (t ^ 2 + a) ≠ 0 →
    y t = Real.log |t + Real.sqrt (t ^ 2 + a)|)
  : deriv y x = 1 / Real.sqrt (x ^ 2 + a) := by
  sorry

/- Exercise 1088, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet ∧ x^{2} + a > 0 ∧ x + sqrtn(2, x^{2} + a) ≠ 0
4. forall (x), x ∈ RealSet ∧ x^{2} + a > 0 ∧ x + sqrtn(2, x^{2} + a) ≠ 0 ⇒ y(x) = ln(|x + sqrtn(2, x^{2} + a)|)
5. FunDeri(y, 1, 1)(x) = frac(1, sqrtn(2, x^{2} + a))

GOAL:
diff(y) = (fun x [x ∈ RealSet ∧ x^{2} + a > 0] . frac(1, sqrtn(2, x^{2} + a))) * diff(fun x [x ∈ RealSet] . x)

METHOD:

-/
theorem proof_gap_exercise_1088_2
  (y : ℝ → ℝ) (a x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ) ∧ 0 < x ^ 2 + a ∧
    x + Real.sqrt (x ^ 2 + a) ≠ 0)
  (h3 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 < t ^ 2 + a ∧
    t + Real.sqrt (t ^ 2 + a) ≠ 0 →
    y t = Real.log |t + Real.sqrt (t ^ 2 + a)|)
  (h4 : deriv y x = 1 / Real.sqrt (x ^ 2 + a))
  : (fun t : {t : ℝ // t ∈ (Set.univ : Set ℝ) ∧ 0 < t ^ 2 + a} =>
      fderiv ℝ y (t : ℝ)) =
    (fun t : {t : ℝ // t ∈ (Set.univ : Set ℝ) ∧ 0 < t ^ 2 + a} =>
      (1 / Real.sqrt ((t : ℝ) ^ 2 + a)) •
        fderiv ℝ (fun s : ℝ => s) (t : ℝ)) := by
  sorry
