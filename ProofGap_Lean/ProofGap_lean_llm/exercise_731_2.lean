import Mathlib

open scoped Topology
open Filter

-- Jump discontinuity for a real-valued function on all of ℝ.
-- The closure-of-domain condition is automatic for domain Set.univ.
def exercise7312JumpSingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ¬ ContinuousAt f a ∧
    ∃ l r : ℝ, Tendsto f (𝓝[<] a) (𝓝 l) ∧
      Tendsto f (𝓝[>] a) (𝓝 r) ∧ l ≠ r

/- Exercise 731_2, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }

GOAL:
lim_{ x → (-1)^- } (f(x)) = 1

METHOD:

-/
theorem proof_gap_exercise_731_2_1
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)) := by
  sorry

/- Exercise 731_2, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }
3. lim_{ x → (-1)^- } (f(x)) = 1

GOAL:
lim_{ x → (-1)^+ } (f(x)) = -1

METHOD:

-/
theorem proof_gap_exercise_731_2_2
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  (h2 : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)))
  : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)) := by
  sorry

/- Exercise 731_2, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }
3. lim_{ x → (-1)^- } (f(x)) = 1
4. lim_{ x → (-1)^+ } (f(x)) = -1

GOAL:
¬ContinuousFuncAt(f, -1)

METHOD:

-/
theorem proof_gap_exercise_731_2_3
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  (h2 : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)))
  (h3 : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)))
  : ¬ ContinuousAt f (-1 : ℝ) := by
  sorry

/- Exercise 731_2, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }
3. lim_{ x → (-1)^- } (f(x)) = 1
4. lim_{ x → (-1)^+ } (f(x)) = -1
5. ¬ContinuousFuncAt(f, -1)

GOAL:
JumpSingularPoint(f, -1)

METHOD:

-/
theorem proof_gap_exercise_731_2_4
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  (h2 : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)))
  (h3 : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)))
  (h4 : ¬ ContinuousAt f (-1 : ℝ))
  : exercise7312JumpSingularPoint f (-1 : ℝ) := by
  sorry

/- Exercise 731_2, gap 5
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }
3. lim_{ x → (-1)^- } (f(x)) = 1
4. lim_{ x → (-1)^+ } (f(x)) = -1
5. ¬ContinuousFuncAt(f, -1)
6. JumpSingularPoint(f, -1)

GOAL:
JumpSingularPoint(f, -1)

METHOD:

-/
theorem proof_gap_exercise_731_2_5
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  (h2 : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)))
  (h3 : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)))
  (h4 : ¬ ContinuousAt f (-1 : ℝ))
  (h5 : exercise7312JumpSingularPoint f (-1 : ℝ))
  : exercise7312JumpSingularPoint f (-1 : ℝ) := by
  sorry

