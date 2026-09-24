import Mathlib

set_option autoImplicit false

-- Inner source binders I are alpha-renamed J, preserving their shadowing.
-- DiffableFuncOn is pointwise ordinary differentiability (source Thm 276/277).

/- Exercise 1023, gap 1
PROOF GAP @1
ASSUM:
1. I = (-∞, 0)
2. f = (fun x [x ∈ RealSet] . 2 * x)
3. g = (fun x [x ∈ RealSet] . x^{2} + 1)

GOAL:
DiffableFuncOn(f, I)

METHOD:
-/
theorem proof_gap_exercise_1023_1
  (I : Set ℝ) (f g : ℝ → ℝ)
  (h1 : I = Set.Iio (0 : ℝ))
  (h2 : f = (fun x : ℝ => 2 * x))
  (h3 : g = (fun x : ℝ => x ^ (2 : ℕ) + 1))
  : ∀ x ∈ I, DifferentiableAt ℝ f x := by
  sorry

/- Exercise 1023, gap 2
PROOF GAP @2
ASSUM:
1. I = (-∞, 0)
2. f = (fun x [x ∈ RealSet] . 2 * x)
3. g = (fun x [x ∈ RealSet] . x^{2} + 1)
4. DiffableFuncOn(f, I)

GOAL:
DiffableFuncOn(g, I)

METHOD:
-/
theorem proof_gap_exercise_1023_2
  (I : Set ℝ) (f g : ℝ → ℝ)
  (h1 : I = Set.Iio (0 : ℝ))
  (h2 : f = (fun x : ℝ => 2 * x))
  (h3 : g = (fun x : ℝ => x ^ (2 : ℕ) + 1))
  (h4 : ∀ x ∈ I, DifferentiableAt ℝ f x)
  : ∀ x ∈ I, DifferentiableAt ℝ g x := by
  sorry

/- Exercise 1023, gap 3
PROOF GAP @3
ASSUM:
1. I = (-∞, 0)
2. f = (fun x [x ∈ RealSet] . 2 * x)
3. g = (fun x [x ∈ RealSet] . x^{2} + 1)
4. DiffableFuncOn(f, I)
5. DiffableFuncOn(g, I)

GOAL:
forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ f(x) ≤ g(x)

METHOD:
-/
theorem proof_gap_exercise_1023_3
  (I : Set ℝ) (f g : ℝ → ℝ)
  (h1 : I = Set.Iio (0 : ℝ))
  (h2 : f = (fun x : ℝ => 2 * x))
  (h3 : g = (fun x : ℝ => x ^ (2 : ℕ) + 1))
  (h4 : ∀ x ∈ I, DifferentiableAt ℝ f x)
  (h5 : ∀ x ∈ I, DifferentiableAt ℝ g x)
  : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → f x ≤ g x := by
  sorry

/- Exercise 1023, gap 4
PROOF GAP @4
ASSUM:
1. I = (-∞, 0)
2. f = (fun x [x ∈ RealSet] . 2 * x)
3. g = (fun x [x ∈ RealSet] . x^{2} + 1)
4. DiffableFuncOn(f, I)
5. DiffableFuncOn(g, I)
6. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ f(x) ≤ g(x)

GOAL:
forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ FunDeri(f, 1, 1)(x) = 2 ∧ FunDeri(g, 1, 1)(x) = 2 * x

METHOD:
-/
theorem proof_gap_exercise_1023_4
  (I : Set ℝ) (f g : ℝ → ℝ)
  (h1 : I = Set.Iio (0 : ℝ))
  (h2 : f = (fun x : ℝ => 2 * x))
  (h3 : g = (fun x : ℝ => x ^ (2 : ℕ) + 1))
  (h4 : ∀ x ∈ I, DifferentiableAt ℝ f x)
  (h5 : ∀ x ∈ I, DifferentiableAt ℝ g x)
  (h6 : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → f x ≤ g x)
  : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → deriv f x = 2 ∧ deriv g x = 2 * x := by
  sorry

/- Exercise 1023, gap 5
PROOF GAP @5
ASSUM:
1. I = (-∞, 0)
2. f = (fun x [x ∈ RealSet] . 2 * x)
3. g = (fun x [x ∈ RealSet] . x^{2} + 1)
4. DiffableFuncOn(f, I)
5. DiffableFuncOn(g, I)
6. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ f(x) ≤ g(x)
7. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ FunDeri(f, 1, 1)(x) = 2 ∧ FunDeri(g, 1, 1)(x) = 2 * x

GOAL:
¬(forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ 2 ≤ 2 * x)

METHOD:
-/
theorem proof_gap_exercise_1023_5
  (I : Set ℝ) (f g : ℝ → ℝ)
  (h1 : I = Set.Iio (0 : ℝ))
  (h2 : f = (fun x : ℝ => 2 * x))
  (h3 : g = (fun x : ℝ => x ^ (2 : ℕ) + 1))
  (h4 : ∀ x ∈ I, DifferentiableAt ℝ f x)
  (h5 : ∀ x ∈ I, DifferentiableAt ℝ g x)
  (h6 : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → f x ≤ g x)
  (h7 : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → deriv f x = 2 ∧ deriv g x = 2 * x)
  : ¬ (∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → 2 ≤ 2 * x) := by
  sorry

/- Exercise 1023, gap 6
PROOF GAP @6
ASSUM:
1. I = (-∞, 0)
2. f = (fun x [x ∈ RealSet] . 2 * x)
3. g = (fun x [x ∈ RealSet] . x^{2} + 1)
4. DiffableFuncOn(f, I)
5. DiffableFuncOn(g, I)
6. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ f(x) ≤ g(x)
7. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ FunDeri(f, 1, 1)(x) = 2 ∧ FunDeri(g, 1, 1)(x) = 2 * x
8. ¬(forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ 2 ≤ 2 * x)

GOAL:
¬(forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ FunDeri(f, 1, 1)(x) ≤ FunDeri(g, 1, 1)(x))

METHOD:
-/
theorem proof_gap_exercise_1023_6
  (I : Set ℝ) (f g : ℝ → ℝ)
  (h1 : I = Set.Iio (0 : ℝ))
  (h2 : f = (fun x : ℝ => 2 * x))
  (h3 : g = (fun x : ℝ => x ^ (2 : ℕ) + 1))
  (h4 : ∀ x ∈ I, DifferentiableAt ℝ f x)
  (h5 : ∀ x ∈ I, DifferentiableAt ℝ g x)
  (h6 : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → f x ≤ g x)
  (h7 : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → deriv f x = 2 ∧ deriv g x = 2 * x)
  (h8 : ¬ (∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → 2 ≤ 2 * x))
  : ¬ (∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → deriv f x ≤ deriv g x) := by
  sorry

/- Exercise 1023, gap 7
PROOF GAP @7
ASSUM:
1. I = (-∞, 0)
2. f = (fun x [x ∈ RealSet] . 2 * x)
3. g = (fun x [x ∈ RealSet] . x^{2} + 1)
4. DiffableFuncOn(f, I)
5. DiffableFuncOn(g, I)
6. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ f(x) ≤ g(x)
7. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ FunDeri(f, 1, 1)(x) = 2 ∧ FunDeri(g, 1, 1)(x) = 2 * x
8. ¬(forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ 2 ≤ 2 * x)
9. ¬(forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ FunDeri(f, 1, 1)(x) ≤ FunDeri(g, 1, 1)(x))

GOAL:
¬(forall (f) (g) (I), f : RealSet → RealSet ∧ g : RealSet → RealSet ∧ I ⊆ RealSet ∧ DiffableFuncOn(f, I) ∧ DiffableFuncOn(g, I) ∧ (forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ f(x) ≤ g(x)) ⇒ (forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ FunDeri(f, 1, 1)(x) ≤ FunDeri(g, 1, 1)(x)))

METHOD:
-/
theorem proof_gap_exercise_1023_7
  (I : Set ℝ) (f g : ℝ → ℝ)
  (h1 : I = Set.Iio (0 : ℝ))
  (h2 : f = (fun x : ℝ => 2 * x))
  (h3 : g = (fun x : ℝ => x ^ (2 : ℕ) + 1))
  (h4 : ∀ x ∈ I, DifferentiableAt ℝ f x)
  (h5 : ∀ x ∈ I, DifferentiableAt ℝ g x)
  (h6 : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → f x ≤ g x)
  (h7 : ∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → deriv f x = 2 ∧ deriv g x = 2 * x)
  (h8 : ¬ (∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → 2 ≤ 2 * x))
  (h9 : ¬ (∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → deriv f x ≤ deriv g x))
  : ¬ (∀ (f g : ℝ → ℝ) (I : Set ℝ),
      I ⊆ (Set.univ : Set ℝ) ∧ (∀ x ∈ I, DifferentiableAt ℝ f x) ∧
      (∀ x ∈ I, DifferentiableAt ℝ g x) ∧
      (∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → f x ≤ g x) →
      (∀ (x : ℝ) (J : Set ℝ), x ∈ (Set.univ : Set ℝ) ∧ J ⊆ (Set.univ : Set ℝ) ∧ x ∈ J → deriv f x ≤ deriv g x)) := by
  sorry
