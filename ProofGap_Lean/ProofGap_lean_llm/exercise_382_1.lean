import Mathlib

namespace Exercise382_1

-- Graphs retain the exact domain of the restricted lambda.
abbrev RealRelation := Set (ℝ × ℝ)

def IsFunc (f : RealRelation) : Prop :=
  ∀ x y₁ y₂ : ℝ, (x, y₁) ∈ f ∧ (x, y₂) ∈ f → y₁ = y₂

def RealArrow (f : RealRelation) : Prop :=
  ∀ x : ℝ, ∃! y : ℝ, (x, y) ∈ f

def reciprocalGraph : RealRelation :=
  {p | p.1 ∈ (Set.univ : Set ℝ) ∧ 0 < p.1 ∧ p.1 < 1 ∧ p.2 = 1 / p.1}

-- Boundedness requires an actual function value at every point of S.
def BoundedFuncOn (f : RealRelation) (S : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x : ℝ, x ∈ S → ∃ y : ℝ, (x, y) ∈ f ∧ |y| ≤ M

-- The source really binds a fresh I here; J is only an alpha-renaming.
def SourceLocal (f : RealRelation) : Prop :=
  ∀ (x : ℝ) (J : Set ℝ),
    x ∈ (Set.univ : Set ℝ) ∧ J ⊆ Set.univ ∧ x ∈ J →
      ∃ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧
        BoundedFuncOn f (Set.Ioo (x - ε) (x + ε) ∩ J)

end Exercise382_1

open Exercise382_1

/- Exercise 382_1, gap 1
PROOF GAP @1
ASSUM:
1. f = (fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . frac(1, x))
2. I = (0, 1)

GOAL:
forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ (exists (`ϵ`), `ϵ` ∈ RealSet ∧ `ϵ` > 0 ∧ BoundedFuncOn(f, IntervalLoRo(x - `ϵ`, x + `ϵ`) ∩ I))

METHOD:

-/
theorem proof_gap_exercise_382_1_1
  (f : RealRelation) (I : Set ℝ)
  (h1 : f = reciprocalGraph)
  (h2 : I = Set.Ioo 0 1)
  : SourceLocal f := by
  sorry

/- Exercise 382_1, gap 2
PROOF GAP @2
ASSUM:
1. f = (fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . frac(1, x))
2. I = (0, 1)
3. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ (exists (`ϵ`), `ϵ` ∈ RealSet ∧ `ϵ` > 0 ∧ BoundedFuncOn(f, IntervalLoRo(x - `ϵ`, x + `ϵ`) ∩ I))

GOAL:
¬BoundedFuncOn(f, I)

METHOD:

-/
theorem proof_gap_exercise_382_1_2
  (f : RealRelation) (I : Set ℝ)
  (h1 : f = reciprocalGraph)
  (h2 : I = Set.Ioo 0 1)
  (h3 : SourceLocal f)
  : ¬ BoundedFuncOn f I := by
  sorry

/- Exercise 382_1, gap 3
PROOF GAP @3
ASSUM:
1. f = (fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . frac(1, x))
2. I = (0, 1)
3. forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ (exists (`ϵ`), `ϵ` ∈ RealSet ∧ `ϵ` > 0 ∧ BoundedFuncOn(f, IntervalLoRo(x - `ϵ`, x + `ϵ`) ∩ I))
4. ¬BoundedFuncOn(f, I)

GOAL:
exists (a) (b), a ∈ RealSet ∧ b ∈ RealSet ∧ a = 0 ∧ b = 1 ∧ ¬(forall (f) (I), f : RealSet → RealSet ∧ I ⊆ RealSet ∧ IsFunc(f) ∧ I = (a, b) ∧ (forall (x) (I), x ∈ RealSet ∧ I ⊆ RealSet ∧ x ∈ I ⇒ (exists (`ϵ`), `ϵ` ∈ RealSet ∧ `ϵ` > 0 ∧ BoundedFuncOn(f, IntervalLoRo(x - `ϵ`, x + `ϵ`) ∩ I))) ⇒ BoundedFuncOn(f, I))

METHOD:

-/
theorem proof_gap_exercise_382_1_3
  (f : RealRelation) (I : Set ℝ)
  (h1 : f = reciprocalGraph)
  (h2 : I = Set.Ioo 0 1)
  (h3 : SourceLocal f)
  (h4 : ¬ BoundedFuncOn f I)
  : ∃ a b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧
      a = 0 ∧ b = 1 ∧ ¬ (∀ (g : RealRelation) (J : Set ℝ),
        RealArrow g ∧ J ⊆ Set.univ ∧ IsFunc g ∧ J = Set.Ioo a b ∧
          SourceLocal g → BoundedFuncOn g J) := by
  sorry

