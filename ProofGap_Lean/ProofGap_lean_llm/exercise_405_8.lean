import Mathlib

open Filter
open scoped Topology

namespace Exercise405_8

-- Defined on a set: every argument in the set has a real function value.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ y : ℝ, f x = y

-- The positive-threshold formulation, with all bounds retained.
def ThresholdCondition (a η : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    ∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x < -E

-- Equality with the restricted lambda, only on its specified domain.
def ExampleCondition (a : ℝ) (f : ℝ → ℝ) : Prop :=
  a = 1 → Set.EqOn f (fun x : ℝ => 1 / (1 - x)) {x : ℝ | x ≠ 1} →
    Tendsto f (𝓝[>] (1 : ℝ)) atBot

end Exercise405_8

open Exercise405_8

/- Exercise 405_8, gap 1
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. lim_{ x → a } (f(x)) = -∞

GOAL:
forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) < -E))

METHOD:

-/
theorem proof_gap_exercise_405_8_1
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hdefined : DefinedOn f (Set.Ioo a (a + η)))
  (hlimit : Tendsto f (𝓝[≠] a) atBot)
  : ThresholdCondition a η f := by
  sorry

/- Exercise 405_8, gap 2
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) < -E))

GOAL:
a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x ≠ 1] . frac(1, 1 - x)) ⇒ lim_{ x → 1^+ } (f(x)) = -∞

METHOD:

-/
theorem proof_gap_exercise_405_8_2
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hdefined : DefinedOn f (Set.Ioo a (a + η)))
  (hthreshold : ThresholdCondition a η f)
  : ExampleCondition a f := by
  sorry

/- Exercise 405_8, gap 3
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) < -E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x ≠ 1] . frac(1, 1 - x)) ⇒ lim_{ x → 1^+ } (f(x)) = -∞

GOAL:
lim_{ x → a^+ } (f(x)) = -∞

METHOD:

-/
theorem proof_gap_exercise_405_8_3
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hdefined : DefinedOn f (Set.Ioo a (a + η)))
  (hthreshold : ThresholdCondition a η f)
  (hexample : ExampleCondition a f)
  : Tendsto f (𝓝[>] a) atBot := by
  sorry

/- Exercise 405_8, gap 4
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) < -E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x ≠ 1] . frac(1, 1 - x)) ⇒ lim_{ x → 1^+ } (f(x)) = -∞
8. lim_{ x → a^+ } (f(x)) = -∞

GOAL:
lim_{ x → a^+ } (f(x)) = -∞

METHOD:

-/
theorem proof_gap_exercise_405_8_4
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hdefined : DefinedOn f (Set.Ioo a (a + η)))
  (hthreshold : ThresholdCondition a η f)
  (hexample : ExampleCondition a f)
  (hlimit : Tendsto f (𝓝[>] a) atBot)
  : Tendsto f (𝓝[>] a) atBot := by
  sorry

