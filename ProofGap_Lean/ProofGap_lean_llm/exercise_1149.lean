import Mathlib

-- Functions are represented by their graphs when comparing different domains.
-- In gap 5 the left domains remain all of ℝ; only the right domains are restricted.
def exercise1149_graphOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ s ∧ p.2 = f p.1}

/- Exercise 1149, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ y(x)^{2} + 2 * ln(y(x)) = x^{4}
3. DiffableFunc(y)
4. DiffableFunc(FunDeri(y, 1, 1))

GOAL:
forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * y(x) * FunDeri(y, 1, 1)(x) + frac(2 * FunDeri(y, 1, 1)(x), y(x)) = 4 * x^{3}

METHOD:
[@method 两边同时对 x 求 导数 @]
-/
theorem proof_gap_exercise_1149_1
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → (y x)^2 + 2 * Real.log (y x) = x^4)
  (h2 : Differentiable ℝ y)
  (h3 : Differentiable ℝ (iteratedDeriv 1 y))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * y x * iteratedDeriv 1 y x + (2 * iteratedDeriv 1 y x) / y x = 4 * x^3 := by
  sorry

/- Exercise 1149, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ y(x)^{2} + 2 * ln(y(x)) = x^{4}
3. DiffableFunc(y)
4. DiffableFunc(FunDeri(y, 1, 1))
5. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * y(x) * FunDeri(y, 1, 1)(x) + frac(2 * FunDeri(y, 1, 1)(x), y(x)) = 4 * x^{3}

GOAL:
forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * FunDeri(y, 1, 1)(x)^{2} + 2 * y(x) * FunDeri(y, 1, 2)(x) + frac(2 * FunDeri(y, 1, 2)(x), y(x)) - frac(2 * FunDeri(y, 1, 1)(x)^{2}, y(x)^{2}) = 12 * x^{2}

METHOD:
[@method 两边同时对 x 求 导数 @]
-/
theorem proof_gap_exercise_1149_2
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → (y x)^2 + 2 * Real.log (y x) = x^4)
  (h2 : Differentiable ℝ y)
  (h3 : Differentiable ℝ (iteratedDeriv 1 y))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * y x * iteratedDeriv 1 y x + (2 * iteratedDeriv 1 y x) / y x = 4 * x^3)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * (iteratedDeriv 1 y x)^2 + 2 * y x * iteratedDeriv 2 y x +
      (2 * iteratedDeriv 2 y x) / y x - (2 * (iteratedDeriv 1 y x)^2) / (y x)^2 = 12 * x^2 := by
  sorry

/- Exercise 1149, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ y(x)^{2} + 2 * ln(y(x)) = x^{4}
3. DiffableFunc(y)
4. DiffableFunc(FunDeri(y, 1, 1))
5. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * y(x) * FunDeri(y, 1, 1)(x) + frac(2 * FunDeri(y, 1, 1)(x), y(x)) = 4 * x^{3}
6. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * FunDeri(y, 1, 1)(x)^{2} + 2 * y(x) * FunDeri(y, 1, 2)(x) + frac(2 * FunDeri(y, 1, 2)(x), y(x)) - frac(2 * FunDeri(y, 1, 1)(x)^{2}, y(x)^{2}) = 12 * x^{2}

GOAL:
forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ FunDeri(y, 1, 1)(x) = frac(2 * x^{3} * y(x), 1 + y(x)^{2})

METHOD:

-/
theorem proof_gap_exercise_1149_3
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → (y x)^2 + 2 * Real.log (y x) = x^4)
  (h2 : Differentiable ℝ y)
  (h3 : Differentiable ℝ (iteratedDeriv 1 y))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * y x * iteratedDeriv 1 y x + (2 * iteratedDeriv 1 y x) / y x = 4 * x^3)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * (iteratedDeriv 1 y x)^2 + 2 * y x * iteratedDeriv 2 y x +
      (2 * iteratedDeriv 2 y x) / y x - (2 * (iteratedDeriv 1 y x)^2) / (y x)^2 = 12 * x^2)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → iteratedDeriv 1 y x = (2 * x^3 * y x) / (1 + (y x)^2) := by
  sorry

/- Exercise 1149, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ y(x)^{2} + 2 * ln(y(x)) = x^{4}
3. DiffableFunc(y)
4. DiffableFunc(FunDeri(y, 1, 1))
5. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * y(x) * FunDeri(y, 1, 1)(x) + frac(2 * FunDeri(y, 1, 1)(x), y(x)) = 4 * x^{3}
6. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * FunDeri(y, 1, 1)(x)^{2} + 2 * y(x) * FunDeri(y, 1, 2)(x) + frac(2 * FunDeri(y, 1, 2)(x), y(x)) - frac(2 * FunDeri(y, 1, 1)(x)^{2}, y(x)^{2}) = 12 * x^{2}
7. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ FunDeri(y, 1, 1)(x) = frac(2 * x^{3} * y(x), 1 + y(x)^{2})

GOAL:
forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ FunDeri(y, 1, 2)(x) = frac(2 * x^{2} * y(x), (1 + y(x)^{2})^{3}) * (3 * (1 + y(x)^{2})^{2} + 2 * x^{4} * (1 - y(x)^{2}))

METHOD:

-/
theorem proof_gap_exercise_1149_4
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → (y x)^2 + 2 * Real.log (y x) = x^4)
  (h2 : Differentiable ℝ y)
  (h3 : Differentiable ℝ (iteratedDeriv 1 y))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * y x * iteratedDeriv 1 y x + (2 * iteratedDeriv 1 y x) / y x = 4 * x^3)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * (iteratedDeriv 1 y x)^2 + 2 * y x * iteratedDeriv 2 y x +
      (2 * iteratedDeriv 2 y x) / y x - (2 * (iteratedDeriv 1 y x)^2) / (y x)^2 = 12 * x^2)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → iteratedDeriv 1 y x = (2 * x^3 * y x) / (1 + (y x)^2))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → iteratedDeriv 2 y x = (2 * x^2 * y x) / (1 + (y x)^2)^3 *
      (3 * (1 + (y x)^2)^2 + 2 * x^4 * (1 - (y x)^2)) := by
  sorry

/- Exercise 1149, gap 5
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ y(x)^{2} + 2 * ln(y(x)) = x^{4}
3. DiffableFunc(y)
4. DiffableFunc(FunDeri(y, 1, 1))
5. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * y(x) * FunDeri(y, 1, 1)(x) + frac(2 * FunDeri(y, 1, 1)(x), y(x)) = 4 * x^{3}
6. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ 2 * FunDeri(y, 1, 1)(x)^{2} + 2 * y(x) * FunDeri(y, 1, 2)(x) + frac(2 * FunDeri(y, 1, 2)(x), y(x)) - frac(2 * FunDeri(y, 1, 1)(x)^{2}, y(x)^{2}) = 12 * x^{2}
7. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ FunDeri(y, 1, 1)(x) = frac(2 * x^{3} * y(x), 1 + y(x)^{2})
8. forall (x), x ∈ RealSet ∧ y(x) > 0 ⇒ FunDeri(y, 1, 2)(x) = frac(2 * x^{2} * y(x), (1 + y(x)^{2})^{3}) * (3 * (1 + y(x)^{2})^{2} + 2 * x^{4} * (1 - y(x)^{2}))

GOAL:
(FunDeri(y, 1, 1), FunDeri(y, 1, 2)) = (fun x [x ∈ RealSet ∧ y(x) > 0] . frac(2 * x^{3} * y(x), 1 + y(x)^{2}), fun x [x ∈ RealSet ∧ y(x) > 0] . frac(2 * x^{2} * y(x), (1 + y(x)^{2})^{3}) * (3 * (1 + y(x)^{2})^{2} + 2 * x^{4} * (1 - y(x)^{2})))

METHOD:

-/
theorem proof_gap_exercise_1149_5
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → (y x)^2 + 2 * Real.log (y x) = x^4)
  (h2 : Differentiable ℝ y)
  (h3 : Differentiable ℝ (iteratedDeriv 1 y))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * y x * iteratedDeriv 1 y x + (2 * iteratedDeriv 1 y x) / y x = 4 * x^3)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → 2 * (iteratedDeriv 1 y x)^2 + 2 * y x * iteratedDeriv 2 y x +
      (2 * iteratedDeriv 2 y x) / y x - (2 * (iteratedDeriv 1 y x)^2) / (y x)^2 = 12 * x^2)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → iteratedDeriv 1 y x = (2 * x^3 * y x) / (1 + (y x)^2))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y x > 0 → iteratedDeriv 2 y x = (2 * x^2 * y x) / (1 + (y x)^2)^3 *
      (3 * (1 + (y x)^2)^2 + 2 * x^4 * (1 - (y x)^2)))
  : (exercise1149_graphOn Set.univ (iteratedDeriv 1 y),
     exercise1149_graphOn Set.univ (iteratedDeriv 2 y)) =
    (exercise1149_graphOn {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ y x > 0}
       (fun x => (2 * x^3 * y x) / (1 + (y x)^2)),
     exercise1149_graphOn {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ y x > 0}
       (fun x => (2 * x^2 * y x) / (1 + (y x)^2)^3 *
         (3 * (1 + (y x)^2)^2 + 2 * x^4 * (1 - (y x)^2)))) := by
  sorry

