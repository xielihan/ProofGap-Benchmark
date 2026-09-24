import Mathlib

-- Sign convention from the theorem library, Thm 206, including sgn(0) = 0.
noncomputable def exercise_744_1_sgn (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x = 0 then 0 else -1

/- Exercise 744_1, gap 1
SHA-256: bcf1800aafb220e7b5cde2e1f59ceb64eefb3f72e3afb66024b29a69b87b5c4b
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = 1 + x^{2}

GOAL:
forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = 1

METHOD:

-/
theorem proof_gap_exercise_744_1_1
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise_744_1_sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = 1 + x ^ (2 : ℕ))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (f ∘ g) x = f (g x) ∧ f (g x) = 1 := by
  sorry

/- Exercise 744_1, gap 2
SHA-256: 627c099453dca1131cbd1b03b3dfb2d4ba87efe92ee9a767c1bd77975613e16a
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = 1 + x^{2}
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = 1

GOAL:
ContinuousFunc(f ∘ g)

METHOD:

-/
theorem proof_gap_exercise_744_1_2
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise_744_1_sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = 1 + x ^ (2 : ℕ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (f ∘ g) x = f (g x) ∧ f (g x) = 1)
  : Continuous (f ∘ g) := by
  sorry

/- Exercise 744_1, gap 3
SHA-256: f3af1d2b17ac20782121412c8d7eade3766982da7566cfae48d14a4e4f4629d1
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = 1 + x^{2}
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = 1
6. ContinuousFunc(f ∘ g)

GOAL:
forall (x), x ∈ RealSet ⇒ g ∘ f(x) = g(f(x)) ∧ g(f(x)) = cases{ 2 if x ≠ 0; 1 if x = 0 }

METHOD:

-/
theorem proof_gap_exercise_744_1_3
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise_744_1_sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = 1 + x ^ (2 : ℕ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (f ∘ g) x = f (g x) ∧ f (g x) = 1)
  (h6 : Continuous (f ∘ g))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (g ∘ f) x = g (f x) ∧ g (f x) = (if x ≠ 0 then 2 else 1) := by
  sorry

/- Exercise 744_1, gap 4
SHA-256: 06ae1df335fa47d731ff37fa7b780e91f7307cacb8360e1b6b9a3c2429a3b95e
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = 1 + x^{2}
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = 1
6. ContinuousFunc(f ∘ g)
7. forall (x), x ∈ RealSet ⇒ g ∘ f(x) = g(f(x)) ∧ g(f(x)) = cases{ 2 if x ≠ 0; 1 if x = 0 }

GOAL:
¬ContinuousFuncAt(g ∘ f, 0)

METHOD:

-/
theorem proof_gap_exercise_744_1_4
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise_744_1_sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = 1 + x ^ (2 : ℕ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (f ∘ g) x = f (g x) ∧ f (g x) = 1)
  (h6 : Continuous (f ∘ g))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (g ∘ f) x = g (f x) ∧ g (f x) = (if x ≠ 0 then 2 else 1))
  : ¬ ContinuousAt (g ∘ f) (0 : ℝ) := by
  sorry

