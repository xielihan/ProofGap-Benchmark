import Mathlib

-- Defined on a set: every input in the set has a real function value.
-- The source final FNFL explicitly types these functions as Real -> Real.
def Exercise742_1.Defined (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ y : ℝ, f x = y

/- Exercise 742_1, gap 1
PROOF GAP @1
ASSUM:
1. f = (fun x [x ∈ RealSet] . 0)
2. g = (fun x [x ∈ RealSet] . cases{ 1 if x ≥ 0; -1 if x < 0 })

GOAL:
ContinuousFunc(f)

METHOD:

-/
theorem proof_gap_exercise_742_1_1
  (f g : ℝ → ℝ)
  (h1 : f = (fun (_x : ℝ) => (0 : ℝ)))
  (h2 : g = (fun (x : ℝ) => if x ≥ 0 then (1 : ℝ) else -1))
  : Continuous f := by
  sorry

/- Exercise 742_1, gap 2
PROOF GAP @2
ASSUM:
1. f = (fun x [x ∈ RealSet] . 0)
2. g = (fun x [x ∈ RealSet] . cases{ 1 if x ≥ 0; -1 if x < 0 })
3. ContinuousFunc(f)

GOAL:
¬ContinuousFuncAt(g, 0)

METHOD:

-/
theorem proof_gap_exercise_742_1_2
  (f g : ℝ → ℝ)
  (h1 : f = (fun (_x : ℝ) => (0 : ℝ)))
  (h2 : g = (fun (x : ℝ) => if x ≥ 0 then (1 : ℝ) else -1))
  (h3 : Continuous f)
  : ¬ ContinuousAt g 0 := by
  sorry

/- Exercise 742_1, gap 3
PROOF GAP @3
ASSUM:
1. f = (fun x [x ∈ RealSet] . 0)
2. g = (fun x [x ∈ RealSet] . cases{ 1 if x ≥ 0; -1 if x < 0 })
3. ContinuousFunc(f)
4. ¬ContinuousFuncAt(g, 0)

GOAL:
forall (x), x ∈ RealSet ⇒ f(x) * g(x) = 0

METHOD:

-/
theorem proof_gap_exercise_742_1_3
  (f g : ℝ → ℝ)
  (h1 : f = (fun (_x : ℝ) => (0 : ℝ)))
  (h2 : g = (fun (x : ℝ) => if x ≥ 0 then (1 : ℝ) else -1))
  (h3 : Continuous f)
  (h4 : ¬ ContinuousAt g 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x * g x = 0 := by
  sorry

/- Exercise 742_1, gap 4
PROOF GAP @4
ASSUM:
1. f = (fun x [x ∈ RealSet] . 0)
2. g = (fun x [x ∈ RealSet] . cases{ 1 if x ≥ 0; -1 if x < 0 })
3. ContinuousFunc(f)
4. ¬ContinuousFuncAt(g, 0)
5. forall (x), x ∈ RealSet ⇒ f(x) * g(x) = 0

GOAL:
ContinuousFunc(fun x [x ∈ RealSet] . f(x) * g(x))

METHOD:

-/
theorem proof_gap_exercise_742_1_4
  (f g : ℝ → ℝ)
  (h1 : f = (fun (_x : ℝ) => (0 : ℝ)))
  (h2 : g = (fun (x : ℝ) => if x ≥ 0 then (1 : ℝ) else -1))
  (h3 : Continuous f)
  (h4 : ¬ ContinuousAt g 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x * g x = 0)
  : Continuous (fun x : ℝ => f x * g x) := by
  sorry

/- Exercise 742_1, gap 5
PROOF GAP @5
ASSUM:
1. f = (fun x [x ∈ RealSet] . 0)
2. g = (fun x [x ∈ RealSet] . cases{ 1 if x ≥ 0; -1 if x < 0 })
3. ContinuousFunc(f)
4. ¬ContinuousFuncAt(g, 0)
5. forall (x), x ∈ RealSet ⇒ f(x) * g(x) = 0
6. ContinuousFunc(fun x [x ∈ RealSet] . f(x) * g(x))

GOAL:
¬(forall (f) (g) (x_{0}), f : RealSet → RealSet ∧ g : RealSet → RealSet ∧ x_{0} ∈ RealSet ∧ (exists (`ϵ`), `ϵ` ∈ RealSet ∧ `ϵ` > 0 ∧ Defined(f, (x_{0} - `ϵ`, x_{0} + `ϵ`)) ∧ Defined(g, (x_{0} - `ϵ`, x_{0} + `ϵ`))) ∧ ContinuousFuncAt(f, x_{0}) ∧ ¬ContinuousFuncAt(g, x_{0}) ⇒ ¬ContinuousFuncAt(fun x [x ∈ RealSet] . f(x) * g(x), x_{0}))

METHOD:

-/
theorem proof_gap_exercise_742_1_5
  (f g : ℝ → ℝ)
  (h1 : f = (fun (_x : ℝ) => (0 : ℝ)))
  (h2 : g = (fun (x : ℝ) => if x ≥ 0 then (1 : ℝ) else -1))
  (h3 : Continuous f)
  (h4 : ¬ ContinuousAt g 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x * g x = 0)
  (h6 : Continuous (fun x : ℝ => f x * g x))
  : ¬ (∀ (F G : ℝ → ℝ) (x₀ : ℝ),
      (x₀ ∈ (Set.univ : Set ℝ) ∧
        (∃ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧
          Exercise742_1.Defined F (Set.Ioo (x₀ - ε) (x₀ + ε)) ∧
          Exercise742_1.Defined G (Set.Ioo (x₀ - ε) (x₀ + ε))) ∧
        ContinuousAt F x₀ ∧ ¬ ContinuousAt G x₀) →
      ¬ ContinuousAt (fun x : ℝ => F x * G x) x₀) := by
  sorry

