import Mathlib

-- exercise: exercise_744_3
-- Sign convention: the theorem library, Thm 206 (including sgn 0 = 0).
noncomputable def exercise7443Sign (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x = 0 then 0 else -1

-- Exercise 744_3, gap 1
/-
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = 1 + x - floor(x)

GOAL:
forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = 1

METHOD:

-/
theorem proof_gap_exercise_744_3_1
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7443Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = 1 + x - (⌊x⌋ : ℤ))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (f ∘ g) x = f (g x) ∧ f (g x) = 1 := by
  sorry

-- Exercise 744_3, gap 2
/-
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = 1 + x - floor(x)
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = 1

GOAL:
ContinuousFunc(f ∘ g)

METHOD:

-/
theorem proof_gap_exercise_744_3_2
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7443Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = 1 + x - (⌊x⌋ : ℤ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (f ∘ g) x = f (g x) ∧ f (g x) = 1)
  : Continuous (f ∘ g) := by
  sorry

-- Exercise 744_3, gap 3
/-
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = 1 + x - floor(x)
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = 1
6. ContinuousFunc(f ∘ g)

GOAL:
forall (x), x ∈ RealSet ⇒ g ∘ f(x) = g(f(x)) ∧ g(f(x)) = 1

METHOD:

-/
theorem proof_gap_exercise_744_3_3
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7443Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = 1 + x - (⌊x⌋ : ℤ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (f ∘ g) x = f (g x) ∧ f (g x) = 1)
  (h6 : Continuous (f ∘ g))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (g ∘ f) x = g (f x) ∧ g (f x) = 1 := by
  sorry

-- Exercise 744_3, gap 4
/-
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = 1 + x - floor(x)
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = 1
6. ContinuousFunc(f ∘ g)
7. forall (x), x ∈ RealSet ⇒ g ∘ f(x) = g(f(x)) ∧ g(f(x)) = 1

GOAL:
ContinuousFunc(g ∘ f)

METHOD:

-/
theorem proof_gap_exercise_744_3_4
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7443Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = 1 + x - (⌊x⌋ : ℤ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (f ∘ g) x = f (g x) ∧ f (g x) = 1)
  (h6 : Continuous (f ∘ g))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (g ∘ f) x = g (f x) ∧ g (f x) = 1)
  : Continuous (g ∘ f) := by
  sorry

