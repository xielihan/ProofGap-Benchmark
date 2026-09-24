import Mathlib

-- Real functions are represented by their graphs, retaining their actual domains.
namespace Exercise764

abbrev RealRelation := Set (ℝ × ℝ)

def IsFunc (f : RealRelation) : Prop :=
  ∀ x y₁ y₂ : ℝ, (x, y₁) ∈ f → (x, y₂) ∈ f → y₁ = y₂

def Dom (f : RealRelation) : Set ℝ := {x | ∃ y, (x, y) ∈ f}

def InverseFunc (f : RealRelation) : RealRelation :=
  {p | (p.2, p.1) ∈ f}

-- A partial relation has value y at x precisely when its fiber is the singleton {y}.
-- This does not select a branch when the inverse has multiple preimages.
def HasValue (f : RealRelation) (x y : ℝ) : Prop :=
  (x, y) ∈ f ∧ ∀ z : ℝ, (x, z) ∈ f → z = y

end Exercise764

open Exercise764

/- Exercise 764, gap 1
SHA-256: f7bd08b083e4fb33c01c94e4c1cdc18513495a5bbe88fc8c7cb49e60b6c8767b
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. IsFunc(f)

GOAL:
forall (x), x ∈ RealSet ⇒ (x ∈ Dom(f) ∧ f(x) ∈ Dom(f) ⇒ InverseFunc(f, x) = f(x) ⇔ x = f(f(x)))

METHOD:

-/
theorem proof_gap_exercise_764_1
    (f : RealRelation) (h_func : IsFunc f) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ y : ℝ, HasValue f x y →
        (x ∈ Dom f ∧ y ∈ Dom f) →
          (HasValue (InverseFunc f) x y ↔ HasValue f y x) := by
  sorry

/- Exercise 764, gap 2
SHA-256: f5476ff3228e49650a5c738dc88c0f09cf6dc58ffd0971d2602562000e15dbca
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. IsFunc(f)
3. forall (x), x ∈ RealSet ⇒ (x ∈ Dom(f) ∧ f(x) ∈ Dom(f) ⇒ InverseFunc(f, x) = f(x) ⇔ x = f(f(x)))

GOAL:
(forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ f(x) ∈ Dom(f) ⇒ x = f(f(x))) ⇒ InverseFunc(f) = f

METHOD:

-/
theorem proof_gap_exercise_764_2
    (f : RealRelation) (h_func : IsFunc f)
    (h_previous : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ y : ℝ, HasValue f x y →
        (x ∈ Dom f ∧ y ∈ Dom f) →
          (HasValue (InverseFunc f) x y ↔ HasValue f y x)) :
    (∀ x : ℝ, ∀ y : ℝ, HasValue f x y →
      (x ∈ (Set.univ : Set ℝ) ∧ x ∈ Dom f ∧ y ∈ Dom f) →
        HasValue f y x) →
      InverseFunc f = f := by
  sorry
