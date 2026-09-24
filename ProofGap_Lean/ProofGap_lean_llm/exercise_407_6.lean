import Mathlib

open Filter
open scoped Topology

namespace Exercise407_6

-- Defined on an interval: the total real function maps each point to a real value.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  Set.MapsTo f s Set.univ

-- Strict approach to b from above, retaining the source epsilon/delta inequalities.
def AboveCondition (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
    ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x - a ∧ x - a < δ →
        0 < f x - b ∧ f x - b < ε

end Exercise407_6

open Exercise407_6

/- Exercise 407_6, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (η), η ∈ RealSet ∧ η > 0 ∧ Defined(f, (a, a + η))

GOAL:
lim_{ x → a^+ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε)))

METHOD:

-/
theorem proof_gap_exercise_407_6_1
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ η : ℝ, η ∈ (Set.univ : Set ℝ) ∧ η > 0 ∧
    DefinedOn f (Set.Ioo a (a + η)))
  : Tendsto f (nhdsWithin a (Set.Ioi a)) (𝓝 b) ↔ AboveCondition f a b := by
  sorry

/- Exercise 407_6, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (η), η ∈ RealSet ∧ η > 0 ∧ Defined(f, (a, a + η))
5. lim_{ x → a^+ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε)))
6. f = (fun x [x ∈ RealSet] . x)
7. a = 0
8. b = 0

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - 0 ∧ x - 0 < δ ⇒ 0 < f(x) - 0 ∧ f(x) - 0 < ε))

METHOD:

-/
theorem proof_gap_exercise_407_6_2
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ η : ℝ, η ∈ (Set.univ : Set ℝ) ∧ η > 0 ∧
    DefinedOn f (Set.Ioo a (a + η)))
  (h5 : Tendsto f (nhdsWithin a (Set.Ioi a)) (𝓝 b) ↔ AboveCondition f a b)
  (h6 : f = fun x : ℝ => x)
  (h7 : a = 0)
  (h8 : b = 0)
  : AboveCondition f 0 0 := by
  sorry

/- Exercise 407_6, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (η), η ∈ RealSet ∧ η > 0 ∧ Defined(f, (a, a + η))
5. lim_{ x → a^+ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε)))
6. f = (fun x [x ∈ RealSet] . x)
7. a = 0
8. b = 0
9. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - 0 ∧ x - 0 < δ ⇒ 0 < f(x) - 0 ∧ f(x) - 0 < ε))

GOAL:
forall (x), x ∈ RealSet ∧ f(x) = x ∧ a = 0 ∧ b = 0 ⇒ lim_{ x → a^+ } (f(x)) = b ∧ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε)))

METHOD:

-/
theorem proof_gap_exercise_407_6_3
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ η : ℝ, η ∈ (Set.univ : Set ℝ) ∧ η > 0 ∧
    DefinedOn f (Set.Ioo a (a + η)))
  (h5 : Tendsto f (nhdsWithin a (Set.Ioi a)) (𝓝 b) ↔ AboveCondition f a b)
  (h6 : f = fun x : ℝ => x)
  (h7 : a = 0)
  (h8 : b = 0)
  (h9 : AboveCondition f 0 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ f x = x ∧ a = 0 ∧ b = 0 →
      Tendsto f (nhdsWithin a (Set.Ioi a)) (𝓝 b) ∧ AboveCondition f a b := by
  sorry
