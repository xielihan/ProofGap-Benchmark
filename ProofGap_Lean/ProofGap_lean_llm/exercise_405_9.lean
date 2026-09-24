import Mathlib

open Filter
open scoped Topology

namespace Exercise405_9

-- A real function with an explicit domain. Values outside the domain are unused.
structure PartialRealFunction where
  domain : Set ℝ
  value : ℝ → ℝ

def Defined (g : PartialRealFunction) (s : Set ℝ) : Prop :=
  s ⊆ g.domain

def totalFunction (f : ℝ → ℝ) : PartialRealFunction :=
  ⟨Set.univ, f⟩

-- Real division requires a nonzero denominator in the source mathematics.
noncomputable def reciprocalExample : PartialRealFunction :=
  ⟨{x | x ≠ 1}, fun x => 1 / (x - 1)⟩

-- Both eventual definedness and divergence are required for a partial function.
def RightInfinite (g : PartialRealFunction) (a : ℝ) : Prop :=
  (∀ᶠ x in nhdsWithin a (Set.Ioi a), x ∈ g.domain) ∧
  Tendsto g.value (nhdsWithin a (Set.Ioi a)) atTop

end Exercise405_9

open Exercise405_9

/- Exercise 405_9, gap 1
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. f : RealSet → RealSet
3. η ∈ RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))

GOAL:
forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))

METHOD:

-/
theorem proof_gap_exercise_405_9_1
  (a : ℝ) (f : ℝ → ℝ) (η : ℝ)
  (h4 : η > 0)
  (h5 : Defined (totalFunction f) (Set.Ioo a (a + η)))
  (h6 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  : (∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E)) := by
  sorry

/- Exercise 405_9, gap 2
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. f : RealSet → RealSet
3. η ∈ RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))
7. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))

GOAL:
lim_{ x → a^+ } (f(x)) = +∞

METHOD:

-/
theorem proof_gap_exercise_405_9_2
  (a : ℝ) (f : ℝ → ℝ) (η : ℝ)
  (h4 : η > 0)
  (h5 : Defined (totalFunction f) (Set.Ioo a (a + η)))
  (h6 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  (h7 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  : (Tendsto f (nhdsWithin a (Set.Ioi a)) atTop) := by
  sorry

/- Exercise 405_9, gap 3
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. f : RealSet → RealSet
3. η ∈ RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))
7. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))
8. lim_{ x → a^+ } (f(x)) = +∞
9. g = (fun x [x ∈ RealSet] . frac(1, x - 1))

GOAL:
Defined(g, RealSet)

METHOD:

-/
theorem proof_gap_exercise_405_9_3
  (a : ℝ) (f : ℝ → ℝ) (η : ℝ)
  (h4 : η > 0)
  (h5 : Defined (totalFunction f) (Set.Ioo a (a + η)))
  (h6 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  (h7 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  (h8 : Tendsto f (nhdsWithin a (Set.Ioi a)) atTop)
  (g : PartialRealFunction)
  (h9 : g = reciprocalExample)
  : (Defined g Set.univ) := by
  sorry

/- Exercise 405_9, gap 4
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. f : RealSet → RealSet
3. η ∈ RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))
7. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))
8. lim_{ x → a^+ } (f(x)) = +∞
9. g = (fun x [x ∈ RealSet] . frac(1, x - 1))
10. Defined(g, RealSet \ {1})

GOAL:
lim_{ x → 1^+ } (g(x)) = +∞

METHOD:

-/
theorem proof_gap_exercise_405_9_4
  (a : ℝ) (f : ℝ → ℝ) (η : ℝ)
  (h4 : η > 0)
  (h5 : Defined (totalFunction f) (Set.Ioo a (a + η)))
  (h6 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  (h7 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  (h8 : Tendsto f (nhdsWithin a (Set.Ioi a)) atTop)
  (g : PartialRealFunction)
  (h9 : g = reciprocalExample)
  (h10 : Defined g ((Set.univ : Set ℝ) \ {1}))
  : (RightInfinite g 1) := by
  sorry

/- Exercise 405_9, gap 5
PROOF GAP @5
ASSUM:
1. a ∈ RealSet
2. f : RealSet → RealSet
3. η ∈ RealSet
4. η > 0
5. Defined(f, (a, a + η))
6. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))
7. forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ δ ≤ η ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ f(x) > E))
8. lim_{ x → a^+ } (f(x)) = +∞
9. g = (fun x [x ∈ RealSet] . frac(1, x - 1))
10. Defined(g, RealSet)
11. lim_{ x → 1^+ } (g(x)) = +∞

GOAL:
lim_{ x → a^+ } (f(x)) = +∞

METHOD:

-/
theorem proof_gap_exercise_405_9_5
  (a : ℝ) (f : ℝ → ℝ) (η : ℝ)
  (h4 : η > 0)
  (h5 : Defined (totalFunction f) (Set.Ioo a (a + η)))
  (h6 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  (h7 : ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧ δ ≤ η ∧
    (∀ x : ℝ, 0 < x - a ∧ x - a < δ → f x > E))
  (h8 : Tendsto f (nhdsWithin a (Set.Ioi a)) atTop)
  (g : PartialRealFunction)
  (h9 : g = reciprocalExample)
  (h10 : Defined g Set.univ)
  (h11 : RightInfinite g 1)
  : (Tendsto f (nhdsWithin a (Set.Ioi a)) atTop) := by
  sorry

