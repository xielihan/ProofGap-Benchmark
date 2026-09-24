import Mathlib

set_option linter.style.longLine false

-- Differentials with respect to the implicit independent real variable t:
-- d^n g = g^(n)(t) (dt)^n. Products are evaluated on the same increment dt.
noncomputable def exercise1179Diff (n : ℕ) (g : ℝ → ℝ) (t dt : ℝ) : ℝ :=
  iteratedDeriv n g t * dt ^ n

-- Literal predicate-library definitions, Thms 285 and 286 (including n = k).
def exercise1179Class (g : ℝ → ℝ) (k : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ k → Differentiable ℝ (iteratedDeriv n g)) ∧
    Continuous (iteratedDeriv k g)

def exercise1179ClassOn (g : ℝ → ℝ) (s : Set ℝ) (k : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ k → DifferentiableOn ℝ (iteratedDeriv n g) s) ∧
    ContinuousOn (iteratedDeriv k g) s

-- y is the real-valued dependent function of t; y = f ∘ x.
-- The original scalar annotation for y describes its values, not a constant function.

/- Exercise 1179, gap 1
PROOF GAP @1
ASSUM:
1. x : RealSet → RealSet ∧ FuncOfClassK(x, 4)
2. y ∈ RealSet
3. f : RealSet → RealSet ∧ FuncOfClassKOn(f, ImageOn(x, Dom(x)), 4)
4. y = f(x)

GOAL:
diff(y) = FunDeri(f, x, 1)(x) * diff(x)

METHOD:

-/
theorem proof_gap_exercise_1179_1
  (x y f : ℝ → ℝ)
  (h1 : exercise1179Class x 4)
  (h2 : ∀ t : ℝ, y t ∈ (Set.univ : Set ℝ))
  (h3 : exercise1179ClassOn f (Set.range x) 4)
  (h4 : y = f ∘ x)
  : ∀ t dt : ℝ, exercise1179Diff 1 y t dt = (iteratedDeriv 1 f (x t)) * (exercise1179Diff 1 x t dt) := by
  sorry

/- Exercise 1179, gap 2
PROOF GAP @2
ASSUM:
1. x : RealSet → RealSet ∧ FuncOfClassK(x, 4)
2. y ∈ RealSet
3. f : RealSet → RealSet ∧ FuncOfClassKOn(f, ImageOn(x, Dom(x)), 4)
4. y = f(x)
5. diff(y) = FunDeri(f, x, 1)(x) * diff(x)

GOAL:
diff^{2}(y) = FunDeri(f, x, 2)(x) * diff(x)^{2} + FunDeri(f, x, 1)(x) * diff^{2}(x)

METHOD:

-/
theorem proof_gap_exercise_1179_2
  (x y f : ℝ → ℝ)
  (h1 : exercise1179Class x 4)
  (h2 : ∀ t : ℝ, y t ∈ (Set.univ : Set ℝ))
  (h3 : exercise1179ClassOn f (Set.range x) 4)
  (h4 : y = f ∘ x)
  (h5 : ∀ t dt : ℝ, exercise1179Diff 1 y t dt = (iteratedDeriv 1 f (x t)) * (exercise1179Diff 1 x t dt))
  : ∀ t dt : ℝ, exercise1179Diff 2 y t dt = (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 2 x t dt) := by
  sorry

/- Exercise 1179, gap 3
PROOF GAP @3
ASSUM:
1. x : RealSet → RealSet ∧ FuncOfClassK(x, 4)
2. y ∈ RealSet
3. f : RealSet → RealSet ∧ FuncOfClassKOn(f, ImageOn(x, Dom(x)), 4)
4. y = f(x)
5. diff(y) = FunDeri(f, x, 1)(x) * diff(x)
6. diff^{2}(y) = FunDeri(f, x, 2)(x) * diff(x)^{2} + FunDeri(f, x, 1)(x) * diff^{2}(x)

GOAL:
diff^{3}(y) = FunDeri(f, x, 3)(x) * diff(x)^{3} + 3 * FunDeri(f, x, 2)(x) * diff(x) * diff^{2}(x) + FunDeri(f, x, 1)(x) * diff^{3}(x)

METHOD:

-/
theorem proof_gap_exercise_1179_3
  (x y f : ℝ → ℝ)
  (h1 : exercise1179Class x 4)
  (h2 : ∀ t : ℝ, y t ∈ (Set.univ : Set ℝ))
  (h3 : exercise1179ClassOn f (Set.range x) 4)
  (h4 : y = f ∘ x)
  (h5 : ∀ t dt : ℝ, exercise1179Diff 1 y t dt = (iteratedDeriv 1 f (x t)) * (exercise1179Diff 1 x t dt))
  (h6 : ∀ t dt : ℝ, exercise1179Diff 2 y t dt = (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 2 x t dt))
  : ∀ t dt : ℝ, exercise1179Diff 3 y t dt = (iteratedDeriv 3 f (x t)) * (exercise1179Diff 1 x t dt) ^ 3 + 3 * (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) * (exercise1179Diff 2 x t dt) + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 3 x t dt) := by
  sorry

/- Exercise 1179, gap 4
PROOF GAP @4
ASSUM:
1. x : RealSet → RealSet ∧ FuncOfClassK(x, 4)
2. y ∈ RealSet
3. f : RealSet → RealSet ∧ FuncOfClassKOn(f, ImageOn(x, Dom(x)), 4)
4. y = f(x)
5. diff(y) = FunDeri(f, x, 1)(x) * diff(x)
6. diff^{2}(y) = FunDeri(f, x, 2)(x) * diff(x)^{2} + FunDeri(f, x, 1)(x) * diff^{2}(x)
7. diff^{3}(y) = FunDeri(f, x, 3)(x) * diff(x)^{3} + 3 * FunDeri(f, x, 2)(x) * diff(x) * diff^{2}(x) + FunDeri(f, x, 1)(x) * diff^{3}(x)

GOAL:
diff^{4}(y) = FunDeri(f, x, 4)(x) * diff(x)^{4} + 3 * FunDeri(f, x, 3)(x) * diff(x)^{2} * diff^{2}(x) + 3 * FunDeri(f, x, 3)(x) * diff(x)^{2} * diff^{2}(x) + 3 * FunDeri(f, x, 2)(x) * (diff^{2}(x)^{2} + diff(x) * diff^{3}(x)) + FunDeri(f, x, 2)(x) * diff(x) * diff^{3}(x) + FunDeri(f, x, 1)(x) * diff^{4}(x)

METHOD:

-/
theorem proof_gap_exercise_1179_4
  (x y f : ℝ → ℝ)
  (h1 : exercise1179Class x 4)
  (h2 : ∀ t : ℝ, y t ∈ (Set.univ : Set ℝ))
  (h3 : exercise1179ClassOn f (Set.range x) 4)
  (h4 : y = f ∘ x)
  (h5 : ∀ t dt : ℝ, exercise1179Diff 1 y t dt = (iteratedDeriv 1 f (x t)) * (exercise1179Diff 1 x t dt))
  (h6 : ∀ t dt : ℝ, exercise1179Diff 2 y t dt = (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 2 x t dt))
  (h7 : ∀ t dt : ℝ, exercise1179Diff 3 y t dt = (iteratedDeriv 3 f (x t)) * (exercise1179Diff 1 x t dt) ^ 3 + 3 * (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) * (exercise1179Diff 2 x t dt) + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 3 x t dt))
  : ∀ t dt : ℝ, exercise1179Diff 4 y t dt = (iteratedDeriv 4 f (x t)) * (exercise1179Diff 1 x t dt) ^ 4 + 3 * (iteratedDeriv 3 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 * (exercise1179Diff 2 x t dt) + 3 * (iteratedDeriv 3 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 * (exercise1179Diff 2 x t dt) + 3 * (iteratedDeriv 2 f (x t)) * ((exercise1179Diff 2 x t dt) ^ 2 + (exercise1179Diff 1 x t dt) * (exercise1179Diff 3 x t dt)) + (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) * (exercise1179Diff 3 x t dt) + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 4 x t dt) := by
  sorry

/- Exercise 1179, gap 5
PROOF GAP @5
ASSUM:
1. x : RealSet → RealSet ∧ FuncOfClassK(x, 4)
2. y ∈ RealSet
3. f : RealSet → RealSet ∧ FuncOfClassKOn(f, ImageOn(x, Dom(x)), 4)
4. y = f(x)
5. diff(y) = FunDeri(f, x, 1)(x) * diff(x)
6. diff^{2}(y) = FunDeri(f, x, 2)(x) * diff(x)^{2} + FunDeri(f, x, 1)(x) * diff^{2}(x)
7. diff^{3}(y) = FunDeri(f, x, 3)(x) * diff(x)^{3} + 3 * FunDeri(f, x, 2)(x) * diff(x) * diff^{2}(x) + FunDeri(f, x, 1)(x) * diff^{3}(x)
8. diff^{4}(y) = FunDeri(f, x, 4)(x) * diff(x)^{4} + 3 * FunDeri(f, x, 3)(x) * diff(x)^{2} * diff^{2}(x) + 3 * FunDeri(f, x, 3)(x) * diff(x)^{2} * diff^{2}(x) + 3 * FunDeri(f, x, 2)(x) * (diff^{2}(x)^{2} + diff(x) * diff^{3}(x)) + FunDeri(f, x, 2)(x) * diff(x) * diff^{3}(x) + FunDeri(f, x, 1)(x) * diff^{4}(x)

GOAL:
diff^{4}(y) = FunDeri(f, x, 4)(x) * diff(x)^{4} + 6 * FunDeri(f, x, 3)(x) * diff(x)^{2} * diff^{2}(x) + 4 * FunDeri(f, x, 2)(x) * diff(x) * diff^{3}(x) + 3 * FunDeri(f, x, 2)(x) * diff^{2}(x)^{2} + FunDeri(f, x, 1)(x) * diff^{4}(x)

METHOD:

-/
theorem proof_gap_exercise_1179_5
  (x y f : ℝ → ℝ)
  (h1 : exercise1179Class x 4)
  (h2 : ∀ t : ℝ, y t ∈ (Set.univ : Set ℝ))
  (h3 : exercise1179ClassOn f (Set.range x) 4)
  (h4 : y = f ∘ x)
  (h5 : ∀ t dt : ℝ, exercise1179Diff 1 y t dt = (iteratedDeriv 1 f (x t)) * (exercise1179Diff 1 x t dt))
  (h6 : ∀ t dt : ℝ, exercise1179Diff 2 y t dt = (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 2 x t dt))
  (h7 : ∀ t dt : ℝ, exercise1179Diff 3 y t dt = (iteratedDeriv 3 f (x t)) * (exercise1179Diff 1 x t dt) ^ 3 + 3 * (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) * (exercise1179Diff 2 x t dt) + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 3 x t dt))
  (h8 : ∀ t dt : ℝ, exercise1179Diff 4 y t dt = (iteratedDeriv 4 f (x t)) * (exercise1179Diff 1 x t dt) ^ 4 + 3 * (iteratedDeriv 3 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 * (exercise1179Diff 2 x t dt) + 3 * (iteratedDeriv 3 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 * (exercise1179Diff 2 x t dt) + 3 * (iteratedDeriv 2 f (x t)) * ((exercise1179Diff 2 x t dt) ^ 2 + (exercise1179Diff 1 x t dt) * (exercise1179Diff 3 x t dt)) + (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) * (exercise1179Diff 3 x t dt) + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 4 x t dt))
  : ∀ t dt : ℝ, exercise1179Diff 4 y t dt = (iteratedDeriv 4 f (x t)) * (exercise1179Diff 1 x t dt) ^ 4 + 6 * (iteratedDeriv 3 f (x t)) * (exercise1179Diff 1 x t dt) ^ 2 * (exercise1179Diff 2 x t dt) + 4 * (iteratedDeriv 2 f (x t)) * (exercise1179Diff 1 x t dt) * (exercise1179Diff 3 x t dt) + 3 * (iteratedDeriv 2 f (x t)) * (exercise1179Diff 2 x t dt) ^ 2 + (iteratedDeriv 1 f (x t)) * (exercise1179Diff 4 x t dt) := by
  sorry
