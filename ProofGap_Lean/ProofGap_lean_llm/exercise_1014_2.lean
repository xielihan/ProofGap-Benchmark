import Mathlib

set_option autoImplicit false

-- Domain is the first projection of the graph (definition Thm 220).
def exercise_1014_2_dom (f : ℝ → ℝ) : Set ℝ :=
  {x | ∃ y : ℝ, f x = y}

-- Gap 5 intentionally retains the source's incompatible total-function type
-- and exact bounded-domain equalities. See the semantic review.

-- Exercise 1014_2, gap 1
/-
PROOF GAP @1
ASSUM:
1. f = (fun x [x ∈ RealSet] . frac(x + |x|, 2))
2. g = (fun x [x ∈ RealSet] . frac(x - |x|, 2))
3. F = (fun x [x ∈ RealSet] . f(x) + g(x))
4. (fun x [x ∈ RealSet] . f(x) + g(x)) = (fun x [x ∈ RealSet] . x)

GOAL:
¬DiffableFuncAt(f, 0)

METHOD:

-/
theorem proof_gap_exercise_1014_2_1
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => (x + |x|) / 2))
  (h2 : g = (fun x : ℝ => (x - |x|) / 2))
  (h3 : F = (fun x : ℝ => f x + g x))
  (h4 : (fun x : ℝ => f x + g x) = (fun x : ℝ => x))
  : ¬ DifferentiableAt ℝ f 0 := by
  sorry

-- Exercise 1014_2, gap 2
/-
PROOF GAP @2
ASSUM:
1. f = (fun x [x ∈ RealSet] . frac(x + |x|, 2))
2. g = (fun x [x ∈ RealSet] . frac(x - |x|, 2))
3. F = (fun x [x ∈ RealSet] . f(x) + g(x))
4. (fun x [x ∈ RealSet] . f(x) + g(x)) = (fun x [x ∈ RealSet] . x)
5. ¬DiffableFuncAt(f, 0)

GOAL:
¬DiffableFuncAt(g, 0)

METHOD:

-/
theorem proof_gap_exercise_1014_2_2
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => (x + |x|) / 2))
  (h2 : g = (fun x : ℝ => (x - |x|) / 2))
  (h3 : F = (fun x : ℝ => f x + g x))
  (h4 : (fun x : ℝ => f x + g x) = (fun x : ℝ => x))
  (h5 : ¬ DifferentiableAt ℝ f 0)
  : ¬ DifferentiableAt ℝ g 0 := by
  sorry

-- Exercise 1014_2, gap 3
/-
PROOF GAP @3
ASSUM:
1. f = (fun x [x ∈ RealSet] . frac(x + |x|, 2))
2. g = (fun x [x ∈ RealSet] . frac(x - |x|, 2))
3. F = (fun x [x ∈ RealSet] . f(x) + g(x))
4. (fun x [x ∈ RealSet] . f(x) + g(x)) = (fun x [x ∈ RealSet] . x)
5. ¬DiffableFuncAt(f, 0)
6. ¬DiffableFuncAt(g, 0)

GOAL:
DiffableFuncAt(F, 0)

METHOD:

-/
theorem proof_gap_exercise_1014_2_3
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => (x + |x|) / 2))
  (h2 : g = (fun x : ℝ => (x - |x|) / 2))
  (h3 : F = (fun x : ℝ => f x + g x))
  (h4 : (fun x : ℝ => f x + g x) = (fun x : ℝ => x))
  (h5 : ¬ DifferentiableAt ℝ f 0)
  (h6 : ¬ DifferentiableAt ℝ g 0)
  : DifferentiableAt ℝ F 0 := by
  sorry

-- Exercise 1014_2, gap 4
/-
PROOF GAP @4
ASSUM:
1. f = (fun x [x ∈ RealSet] . frac(x + |x|, 2))
2. g = (fun x [x ∈ RealSet] . frac(x - |x|, 2))
3. F = (fun x [x ∈ RealSet] . f(x) + g(x))
4. (fun x [x ∈ RealSet] . f(x) + g(x)) = (fun x [x ∈ RealSet] . x)
5. ¬DiffableFuncAt(f, 0)
6. ¬DiffableFuncAt(g, 0)
7. DiffableFuncAt(F, 0)

GOAL:
FunDeri(F, 1, 1)(0) = 1

METHOD:

-/
theorem proof_gap_exercise_1014_2_4
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => (x + |x|) / 2))
  (h2 : g = (fun x : ℝ => (x - |x|) / 2))
  (h3 : F = (fun x : ℝ => f x + g x))
  (h4 : (fun x : ℝ => f x + g x) = (fun x : ℝ => x))
  (h5 : ¬ DifferentiableAt ℝ f 0)
  (h6 : ¬ DifferentiableAt ℝ g 0)
  (h7 : DifferentiableAt ℝ F 0)
  : deriv F 0 = 1 := by
  sorry

-- Exercise 1014_2, gap 5
/-
PROOF GAP @5
ASSUM:
1. f = (fun x [x ∈ RealSet] . frac(x + |x|, 2))
2. g = (fun x [x ∈ RealSet] . frac(x - |x|, 2))
3. F = (fun x [x ∈ RealSet] . f(x) + g(x))
4. (fun x [x ∈ RealSet] . f(x) + g(x)) = (fun x [x ∈ RealSet] . x)
5. ¬DiffableFuncAt(f, 0)
6. ¬DiffableFuncAt(g, 0)
7. DiffableFuncAt(F, 0)
8. FunDeri(F, 1, 1)(0) = 1

GOAL:
¬(forall (f) (g) (F) (x_{0}), f : RealSet → RealSet ∧ g : RealSet → RealSet ∧ F : RealSet → RealSet ∧ x_{0} ∈ RealSet ∧ (exists (`ϵ`), `ϵ` ∈ RealSet ∧ `ϵ` > 0 ∧ Dom(f) = (x_{0} - `ϵ`, x_{0} + `ϵ`)) ∧ (exists (`ϵ`), `ϵ` ∈ RealSet ∧ `ϵ` > 0 ∧ Dom(g) = (x_{0} - `ϵ`, x_{0} + `ϵ`)) ∧ ¬DiffableFuncAt(f, x_{0}) ∧ ¬DiffableFuncAt(g, x_{0}) ∧ F = f + g ⇒ ¬DiffableFuncAt(F, x_{0}))

METHOD:

-/
theorem proof_gap_exercise_1014_2_5
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => (x + |x|) / 2))
  (h2 : g = (fun x : ℝ => (x - |x|) / 2))
  (h3 : F = (fun x : ℝ => f x + g x))
  (h4 : (fun x : ℝ => f x + g x) = (fun x : ℝ => x))
  (h5 : ¬ DifferentiableAt ℝ f 0)
  (h6 : ¬ DifferentiableAt ℝ g 0)
  (h7 : DifferentiableAt ℝ F 0)
  (h8 : deriv F 0 = 1)
  : ¬ (∀ (f g F : ℝ → ℝ) (x₀ : ℝ),
      x₀ ∈ (Set.univ : Set ℝ) ∧
      (∃ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧
        exercise_1014_2_dom f = Set.Ioo (x₀ - ε) (x₀ + ε)) ∧
      (∃ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧
        exercise_1014_2_dom g = Set.Ioo (x₀ - ε) (x₀ + ε)) ∧
      ¬ DifferentiableAt ℝ f x₀ ∧
      ¬ DifferentiableAt ℝ g x₀ ∧ F = f + g →
      ¬ DifferentiableAt ℝ F x₀) := by
  sorry

