import Mathlib

namespace Exercise227

-- Restricted function graph (definition of RestrictFunc, Thm 226).
def restrictedGraph (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ s ∧ p.2 = f p.1}

-- InverseFunc is the converse relation (Thm 221).
def inverseGraph (r : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | (p.2, p.1) ∈ r}

-- A function value equals v precisely when its fiber is the singleton {v}.
-- This includes existence and uniqueness and does not totalize a partial inverse.
def valueEq (r : Set (ℝ × ℝ)) (t v : ℝ) : Prop :=
  ∀ x : ℝ, (t, x) ∈ r ↔ x = v

/- Exercise 227, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ -1 ≤ x ∧ x ≤ 1 ⇒ y(x) = sqrtn(2, 1 - x^{2})

GOAL:
forall (t), t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1 ⇒ InverseFunc(RestrictFunc(y, [-1, 0]), t) = -sqrtn(2, 1 - t^{2})

METHOD:

-/
theorem proof_gap_exercise_227_1
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, -1 ≤ x ∧ x ≤ 1 → y x = Real.sqrt (1 - x ^ 2))
  : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 →
    valueEq (inverseGraph (restrictedGraph y (Set.Icc (-1) 0))) t (-Real.sqrt (1 - t ^ 2)) := by
  sorry

/- Exercise 227, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ -1 ≤ x ∧ x ≤ 1 ⇒ y(x) = sqrtn(2, 1 - x^{2})
3. forall (t), t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1 ⇒ InverseFunc(RestrictFunc(y, [-1, 0]), t) = -sqrtn(2, 1 - t^{2})

GOAL:
InverseFunc(RestrictFunc(y, [-1, 0])) = (fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1] . -sqrtn(2, 1 - t^{2}))

METHOD:

-/
theorem proof_gap_exercise_227_2
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, -1 ≤ x ∧ x ≤ 1 → y x = Real.sqrt (1 - x ^ 2))
  (h2 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 →
    valueEq (inverseGraph (restrictedGraph y (Set.Icc (-1) 0))) t (-Real.sqrt (1 - t ^ 2)))
  : inverseGraph (restrictedGraph y (Set.Icc (-1) 0)) =
    restrictedGraph (fun t => -Real.sqrt (1 - t ^ 2)) (Set.Icc 0 1) := by
  sorry

/- Exercise 227, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ -1 ≤ x ∧ x ≤ 1 ⇒ y(x) = sqrtn(2, 1 - x^{2})
3. forall (t), t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1 ⇒ InverseFunc(RestrictFunc(y, [-1, 0]), t) = -sqrtn(2, 1 - t^{2})
4. InverseFunc(RestrictFunc(y, [-1, 0])) = (fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1] . -sqrtn(2, 1 - t^{2}))

GOAL:
forall (t), t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1 ⇒ InverseFunc(RestrictFunc(y, [0, 1]), t) = sqrtn(2, 1 - t^{2})

METHOD:

-/
theorem proof_gap_exercise_227_3
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, -1 ≤ x ∧ x ≤ 1 → y x = Real.sqrt (1 - x ^ 2))
  (h2 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 →
    valueEq (inverseGraph (restrictedGraph y (Set.Icc (-1) 0))) t (-Real.sqrt (1 - t ^ 2)))
  (h3 : inverseGraph (restrictedGraph y (Set.Icc (-1) 0)) =
    restrictedGraph (fun t => -Real.sqrt (1 - t ^ 2)) (Set.Icc 0 1))
  : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 →
    valueEq (inverseGraph (restrictedGraph y (Set.Icc 0 1))) t (Real.sqrt (1 - t ^ 2)) := by
  sorry

/- Exercise 227, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ -1 ≤ x ∧ x ≤ 1 ⇒ y(x) = sqrtn(2, 1 - x^{2})
3. forall (t), t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1 ⇒ InverseFunc(RestrictFunc(y, [-1, 0]), t) = -sqrtn(2, 1 - t^{2})
4. InverseFunc(RestrictFunc(y, [-1, 0])) = (fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1] . -sqrtn(2, 1 - t^{2}))
5. forall (t), t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1 ⇒ InverseFunc(RestrictFunc(y, [0, 1]), t) = sqrtn(2, 1 - t^{2})

GOAL:
InverseFunc(RestrictFunc(y, [0, 1])) = (fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ 1] . sqrtn(2, 1 - t^{2}))

METHOD:

-/
theorem proof_gap_exercise_227_4
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, -1 ≤ x ∧ x ≤ 1 → y x = Real.sqrt (1 - x ^ 2))
  (h2 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 →
    valueEq (inverseGraph (restrictedGraph y (Set.Icc (-1) 0))) t (-Real.sqrt (1 - t ^ 2)))
  (h3 : inverseGraph (restrictedGraph y (Set.Icc (-1) 0)) =
    restrictedGraph (fun t => -Real.sqrt (1 - t ^ 2)) (Set.Icc 0 1))
  (h4 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 →
    valueEq (inverseGraph (restrictedGraph y (Set.Icc 0 1))) t (Real.sqrt (1 - t ^ 2)))
  : inverseGraph (restrictedGraph y (Set.Icc 0 1)) =
    restrictedGraph (fun t => Real.sqrt (1 - t ^ 2)) (Set.Icc 0 1) := by
  sorry

end Exercise227
