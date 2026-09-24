import Mathlib

open Filter
open scoped Topology

namespace Exercise405_7

-- Defined on a set: every input in that set has a real output.
-- With the source's total real function type this is automatic, but retained explicitly.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  Set.MapsTo f s Set.univ

-- The textbook's unsigned infinity means divergence of the absolute value.
def RightUnsignedInfinity (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun x => |f x|) (𝓝[>] a) atTop

def RightBound (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧
    ∀ x : ℝ, 0 < x - a ∧ x - a < δ → |f x| > E

-- Equality to a restricted lambda means equality on its stated domain.
-- No value of f outside (1, ∞) is prescribed.
def ExampleOnDomain (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x > 1 → f x = (-1 : ℝ) ^ (⌊1 / (x - 1)⌋ : ℤ) / (x - 1)

def ExampleClaim (f : ℝ → ℝ) (a : ℝ) : Prop :=
  a = 1 → ExampleOnDomain f → RightUnsignedInfinity f 1

end Exercise405_7

open Exercise405_7

/- Exercise 405_7, gap 1
SHA-256: 4c1b93e7abed0ac9f525e3aa0b777425af22aa9c254e08b86765d5176e6bd58e
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. lim_{ x → a } (f(x)) = +∞

GOAL:
forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ |f(x)| > E))

METHOD:

-/
theorem proof_gap_exercise_405_7_1
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo a (a + η)))
  (hLimit : Tendsto f (𝓝[≠] a) atTop)
  : RightBound f a := by
  sorry

/- Exercise 405_7, gap 2
SHA-256: fb4b3aa4ce8e29002a4e46d947f3008841a1dffe3490c1e349898e013165c04f
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ |f(x)| > E))

GOAL:
a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x > 1] . frac((-1)^{floor(frac(1, x - 1))}, x - 1)) ⇒ lim_{ x → 1^+ } (f(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_405_7_2
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo a (a + η)))
  (hBound : RightBound f a)
  : ExampleClaim f a := by
  sorry

/- Exercise 405_7, gap 3
SHA-256: 99d3f7f2719b99ca375774bd473a564c0c26a4f931cc833acab21e97e21bd151
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ |f(x)| > E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x > 1] . frac((-1)^{floor(frac(1, x - 1))}, x - 1)) ⇒ lim_{ x → 1^+ } (f(x)) = ∞

GOAL:
lim_{ x → a^+ } (f(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_405_7_3
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo a (a + η)))
  (hBound : RightBound f a)
  (hExample : ExampleClaim f a)
  : RightUnsignedInfinity f a := by
  sorry

/- Exercise 405_7, gap 4
SHA-256: 111344377ca5fa24d1b03c9e38e978211eb4938a38567fd8942fa4f4839d8a3d
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. η ∈ RealSet
3. f : RealSet → RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ |f(x)| > E))
7. a = 1 ⇒ f = (fun x [x ∈ RealSet ∧ x > 1] . frac((-1)^{floor(frac(1, x - 1))}, x - 1)) ⇒ lim_{ x → 1^+ } (f(x)) = ∞
8. lim_{ x → a^+ } (f(x)) = ∞

GOAL:
lim_{ x → a^+ } (f(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_405_7_4
  (a η : ℝ) (f : ℝ → ℝ)
  (hη : η > 0)
  (hDefined : DefinedOn f (Set.Ioo a (a + η)))
  (hBound : RightBound f a)
  (hExample : ExampleClaim f a)
  (hLimit : RightUnsignedInfinity f a)
  : RightUnsignedInfinity f a := by
  sorry
