import Mathlib

open Filter
open scoped Topology

namespace Exercise405_5

-- A total real-valued function is defined on s when each input in s has a value.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ y : ℝ, f x = y

-- Equality with the restricted function imposes values only on x < 1.
def ReciprocalOnLeft (f : ℝ → ℝ) : Prop :=
  Set.EqOn f (fun x : ℝ => 1 / (x - 1)) (Set.Iio 1)

def LeftNegInfinity (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto f (nhdsWithin a (Set.Iio a)) atBot

def NegInfinityCondition (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧
    ∀ x : ℝ, 0 < a - x ∧ a - x < δ → f x < -E

/- Exercise 405_5, gap 1
SHA-256: 803ec36b46fa56ff457d4338c28a88a6b4f366a3c107a725a12090c25b2663b5
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. lim_{ x → a } (f(x)) = -∞

GOAL:
forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ f(x) < -E))

METHOD:

-/
theorem proof_gap_exercise_405_5_1
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hLimit : Tendsto f (nhdsWithin a ({a}ᶜ : Set ℝ)) atBot)
  : NegInfinityCondition f a := by
  sorry

/- Exercise 405_5, gap 2
SHA-256: d0f61f44f9d4cf0091407d33d0f5e5b050d3e63737d887f6cd7d400459984e6e
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ f(x) < -E))

GOAL:
a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac(1, x - 1)) ⇒ lim_{ x → 1^- } (f(x)) = -∞

METHOD:

-/
theorem proof_gap_exercise_405_5_2
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hCondition : NegInfinityCondition f a)
  : a = 1 → ReciprocalOnLeft f → LeftNegInfinity f 1 := by
  sorry

/- Exercise 405_5, gap 3
SHA-256: 89ee51968dd882d6dbc5db1d7eba3eefdf05125a7551446df40f7452e46d97bc
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ f(x) < -E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac(1, x - 1)) ⇒ lim_{ x → 1^- } (f(x)) = -∞

GOAL:
lim_{ x → a^- } (f(x)) = -∞

METHOD:

-/
theorem proof_gap_exercise_405_5_3
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hCondition : NegInfinityCondition f a)
  (hExample : a = 1 → ReciprocalOnLeft f → LeftNegInfinity f 1)
  : LeftNegInfinity f a := by
  sorry

/- Exercise 405_5, gap 4
SHA-256: 6ab795e695708243cfef657f15162b870be47e1dfbcc218ba9a070edbc1a261d
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ f(x) < -E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac(1, x - 1)) ⇒ lim_{ x → 1^- } (f(x)) = -∞
8. lim_{ x → a^- } (f(x)) = -∞

GOAL:
lim_{ x → a^- } (f(x)) = -∞

METHOD:

-/
theorem proof_gap_exercise_405_5_4
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hCondition : NegInfinityCondition f a)
  (hExample : a = 1 → ReciprocalOnLeft f → LeftNegInfinity f 1)
  (hLimit : LeftNegInfinity f a)
  : LeftNegInfinity f a := by
  sorry

end Exercise405_5
