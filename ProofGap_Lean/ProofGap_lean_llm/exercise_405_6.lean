import Mathlib

open Filter
open scoped Topology

namespace Exercise405_6

-- The source types f as a total real function. Defined records real-valued
-- evaluation on the stated interval; no continuity or boundedness is imposed.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ y : ℝ, f x = y

-- Positive-threshold formulation, with exactly the source's unrestricted x binder.
def PositiveThreshold (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧
    ∀ x : ℝ, 0 < a - x ∧ a - x < δ → f x > E

-- Equality with the restricted lambda means equality on its given domain.
def ReciprocalExample (f : ℝ → ℝ) (a : ℝ) : Prop :=
  a = 1 → Set.EqOn f (fun x : ℝ => 1 / (1 - x)) (Set.Iio 1) →
    Tendsto f (𝓝[<] (1 : ℝ)) atTop

/- Exercise 405_6, gap 1
SHA-256: 96c23170412b644719f8a44144f04720c5d93a71ba0bc15779d95ea0325abb20
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. lim_{ x → a } (f(x)) = +∞

GOAL:
forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ f(x) > E))

METHOD:

-/
theorem proof_gap_exercise_405_6_1
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hLimit : Tendsto f (𝓝[≠] a) atTop)
  : PositiveThreshold f a := by
  sorry

/- Exercise 405_6, gap 2
SHA-256: 7a4f1faec2108fea3dbc01d5616ca086ad1553b37b6d9b4f3b9df89a333b51fe
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ f(x) > E))

GOAL:
a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac(1, 1 - x)) ⇒ lim_{ x → 1^- } (f(x)) = +∞

METHOD:

-/
theorem proof_gap_exercise_405_6_2
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hThreshold : PositiveThreshold f a)
  : ReciprocalExample f a := by
  sorry

/- Exercise 405_6, gap 3
SHA-256: 75397a1211c127c5502bb1c2d2d87d5e35137c6350cc2e5a53ba9872c571a803
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ f(x) > E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac(1, 1 - x)) ⇒ lim_{ x → 1^- } (f(x)) = +∞

GOAL:
lim_{ x → a^- } (f(x)) = +∞

METHOD:

-/
theorem proof_gap_exercise_405_6_3
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hThreshold : PositiveThreshold f a)
  (hExample : ReciprocalExample f a)
  : Tendsto f (𝓝[<] a) atTop := by
  sorry

/- Exercise 405_6, gap 4
SHA-256: f6824a6f51410533de28af2b29effd5ae47a9d9a93de96cbc22a8a90b15298b9
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ f(x) > E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac(1, 1 - x)) ⇒ lim_{ x → 1^- } (f(x)) = +∞
8. lim_{ x → a^- } (f(x)) = +∞

GOAL:
lim_{ x → a^- } (f(x)) = +∞

METHOD:

-/
theorem proof_gap_exercise_405_6_4
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hThreshold : PositiveThreshold f a)
  (hExample : ReciprocalExample f a)
  (hLeftLimit : Tendsto f (𝓝[<] a) atTop)
  : Tendsto f (𝓝[<] a) atTop := by
  sorry

end Exercise405_6
