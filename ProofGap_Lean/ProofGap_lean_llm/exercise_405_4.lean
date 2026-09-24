import Mathlib

open Filter
open scoped Topology

namespace Exercise405_4

-- Defined means each point of the stated interval has a real function value.
-- With the source's total type ℝ → ℝ this is automatic, but retained explicitly.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ y : ℝ, f x = y

def LeftMagnitudeCondition (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧
    ∀ x : ℝ, 0 < a - x ∧ a - x < δ → |f x| > E

def LeftUnsignedInfinity (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun x => |f x|) (𝓝[<] a) atTop

-- Equality with the restricted lambda imposes values only on x < 1.
noncomputable def ExampleCondition (f : ℝ → ℝ) (a : ℝ) : Prop :=
  a = 1 →
    Set.EqOn f (fun x : ℝ => (-1 : ℝ) ^ (⌊1 / (1 - x)⌋ : ℤ) / (1 - x))
      (Set.Iio (1 : ℝ)) →
    LeftUnsignedInfinity f 1

end Exercise405_4

open Exercise405_4

/- Exercise 405_4, gap 1
SHA-256: 51ab28a4beb250aaeabcc9983c4f03f32eb62534653e73faf68aa90cb8434dbb
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. lim_{ x → a } (f(x)) = +∞

GOAL:
forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ |f(x)| > E))

METHOD:

-/
theorem proof_gap_exercise_405_4_1
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hLimit : Tendsto f (𝓝[≠] a) atTop)
  : LeftMagnitudeCondition f a := by
  sorry

/- Exercise 405_4, gap 2
SHA-256: 9aa16213fb099844feef1fb8d0f1ff42381a0a3f39c361a521451606b13b9b5a
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ |f(x)| > E))

GOAL:
a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac((-1)^{floor(frac(1, 1 - x))}, 1 - x)) ⇒ lim_{ x → 1^- } (f(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_405_4_2
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hMagnitude : LeftMagnitudeCondition f a)
  : ExampleCondition f a := by
  sorry

/- Exercise 405_4, gap 3
SHA-256: f898d3330b874ce7e8afc99b5b0c1b58671ef6c76808cb0b8a062d8b798acfd2
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ |f(x)| > E))
7. ¬(a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac((-1)^{floor(frac(1, 1 - x))}, 1 - x)) ⇒ lim_{ x → 1^- } (f(x)) = ∞)

GOAL:
lim_{ x → a^- } (f(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_405_4_3
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hMagnitude : LeftMagnitudeCondition f a)
  (hNotExample : ¬ ExampleCondition f a)
  : LeftUnsignedInfinity f a := by
  sorry

/- Exercise 405_4, gap 4
SHA-256: 97416e98bb8ff3edf64c98bb0b106c4149d247835ae710609b36bb4c49fed6ab
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a - η, a))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ |f(x)| > E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x < 1] . frac((-1)^{floor(frac(1, 1 - x))}, 1 - x)) ⇒ lim_{ x → 1^- } (f(x)) = ∞
8. lim_{ x → a^- } (f(x)) = ∞

GOAL:
lim_{ x → a^- } (f(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_405_4_4
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo (a - η) a))
  (hMagnitude : LeftMagnitudeCondition f a)
  (hExample : ExampleCondition f a)
  (hLimit : LeftUnsignedInfinity f a)
  : LeftUnsignedInfinity f a := by
  sorry

