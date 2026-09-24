import Mathlib

-- All functions have domain and codomain ℝ.
-- The sign definition includes sgn(0) = 0 (source definition 206).
noncomputable def exercise7442Sign (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x = 0 then 0 else -1

-- The seven source regions are disjoint and exhaust ℝ.
-- Thus the last fallback is unreachable and does not extend the source domain.
noncomputable def exercise7442Cases (x : ℝ) : ℝ :=
  if x < -1 then 1 else
  if x = -1 then 0 else
  if -1 < x ∧ x < 0 then -1 else
  if x = 0 then 0 else
  if 0 < x ∧ x < 1 then 1 else
  if x = 1 then 0 else
  if x > 1 then -1 else -1

/- Exercise 744_2, gap 1
SHA-256: 9118defe96c6ebf517691990b8c46c605ce7d2435d3c8502c9405f597fc02e37
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = x * (1 - x^{2})

GOAL:
forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = cases{ 1 if x < -1; 0 if x = -1; -1 if -1 < x ∧ x < 0; 0 if x = 0; 1 if 0 < x ∧ x < 1; 0 if x = 1; -1 if x > 1 }

METHOD:

-/
theorem proof_gap_exercise_744_2_1
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7442Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = x * (1 - x ^ 2))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    (f ∘ g) x = f (g x) ∧ f (g x) = exercise7442Cases x := by
  sorry

/- Exercise 744_2, gap 2
SHA-256: f0b569287cf425505753bb205d74cd708ebb0220376eb0c177aa87dfd561c9d2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = x * (1 - x^{2})
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = cases{ 1 if x < -1; 0 if x = -1; -1 if -1 < x ∧ x < 0; 0 if x = 0; 1 if 0 < x ∧ x < 1; 0 if x = 1; -1 if x > 1 }

GOAL:
¬ContinuousFuncAt(f ∘ g, -1)

METHOD:

-/
theorem proof_gap_exercise_744_2_2
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7442Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = x * (1 - x ^ 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    (f ∘ g) x = f (g x) ∧ f (g x) = exercise7442Cases x)
  : ¬ContinuousAt (f ∘ g) (-1 : ℝ) := by
  sorry

/- Exercise 744_2, gap 3
SHA-256: 75ffc70829e7ed2870567af5752d3215a439c91f762ea51ade03cef8cc0b21fa
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = x * (1 - x^{2})
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = cases{ 1 if x < -1; 0 if x = -1; -1 if -1 < x ∧ x < 0; 0 if x = 0; 1 if 0 < x ∧ x < 1; 0 if x = 1; -1 if x > 1 }
6. ¬ContinuousFuncAt(f ∘ g, -1)

GOAL:
¬ContinuousFuncAt(f ∘ g, 0)

METHOD:

-/
theorem proof_gap_exercise_744_2_3
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7442Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = x * (1 - x ^ 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    (f ∘ g) x = f (g x) ∧ f (g x) = exercise7442Cases x)
  (h6 : ¬ContinuousAt (f ∘ g) (-1 : ℝ))
  : ¬ContinuousAt (f ∘ g) (0 : ℝ) := by
  sorry

/- Exercise 744_2, gap 4
SHA-256: 75c8bfb210b64cf3fdb6edda1fff923584378afa5361553413c7794c40f0b5d2
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = x * (1 - x^{2})
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = cases{ 1 if x < -1; 0 if x = -1; -1 if -1 < x ∧ x < 0; 0 if x = 0; 1 if 0 < x ∧ x < 1; 0 if x = 1; -1 if x > 1 }
6. ¬ContinuousFuncAt(f ∘ g, -1)
7. ¬ContinuousFuncAt(f ∘ g, 0)

GOAL:
¬ContinuousFuncAt(f ∘ g, 1)

METHOD:

-/
theorem proof_gap_exercise_744_2_4
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7442Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = x * (1 - x ^ 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    (f ∘ g) x = f (g x) ∧ f (g x) = exercise7442Cases x)
  (h6 : ¬ContinuousAt (f ∘ g) (-1 : ℝ))
  (h7 : ¬ContinuousAt (f ∘ g) (0 : ℝ))
  : ¬ContinuousAt (f ∘ g) (1 : ℝ) := by
  sorry

/- Exercise 744_2, gap 5
SHA-256: f89a2f94f5ec0b0d501e0427226e5bf1d1704c81003286884221ae638f8f89a6
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = x * (1 - x^{2})
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = cases{ 1 if x < -1; 0 if x = -1; -1 if -1 < x ∧ x < 0; 0 if x = 0; 1 if 0 < x ∧ x < 1; 0 if x = 1; -1 if x > 1 }
6. ¬ContinuousFuncAt(f ∘ g, -1)
7. ¬ContinuousFuncAt(f ∘ g, 0)
8. ¬ContinuousFuncAt(f ∘ g, 1)

GOAL:
forall (x), x ∈ RealSet ⇒ g ∘ f(x) = g(f(x)) ∧ g(f(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_744_2_5
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7442Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = x * (1 - x ^ 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    (f ∘ g) x = f (g x) ∧ f (g x) = exercise7442Cases x)
  (h6 : ¬ContinuousAt (f ∘ g) (-1 : ℝ))
  (h7 : ¬ContinuousAt (f ∘ g) (0 : ℝ))
  (h8 : ¬ContinuousAt (f ∘ g) (1 : ℝ))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    (g ∘ f) x = g (f x) ∧ g (f x) = 0 := by
  sorry

/- Exercise 744_2, gap 6
SHA-256: 398a371d4d9eb1805e11afa063302c427c7a328229339eb965c4538bef7f6457
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. g : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ f(x) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ g(x) = x * (1 - x^{2})
5. forall (x), x ∈ RealSet ⇒ f ∘ g(x) = f(g(x)) ∧ f(g(x)) = cases{ 1 if x < -1; 0 if x = -1; -1 if -1 < x ∧ x < 0; 0 if x = 0; 1 if 0 < x ∧ x < 1; 0 if x = 1; -1 if x > 1 }
6. ¬ContinuousFuncAt(f ∘ g, -1)
7. ¬ContinuousFuncAt(f ∘ g, 0)
8. ¬ContinuousFuncAt(f ∘ g, 1)
9. forall (x), x ∈ RealSet ⇒ g ∘ f(x) = g(f(x)) ∧ g(f(x)) = 0

GOAL:
ContinuousFunc(g ∘ f)

METHOD:

-/
theorem proof_gap_exercise_744_2_6
  (f g : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = exercise7442Sign x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → g x = x * (1 - x ^ 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    (f ∘ g) x = f (g x) ∧ f (g x) = exercise7442Cases x)
  (h6 : ¬ContinuousAt (f ∘ g) (-1 : ℝ))
  (h7 : ¬ContinuousAt (f ∘ g) (0 : ℝ))
  (h8 : ¬ContinuousAt (f ∘ g) (1 : ℝ))
  (h9 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    (g ∘ f) x = g (f x) ∧ g (f x) = 0)
  : Continuous (g ∘ f) := by
  sorry

