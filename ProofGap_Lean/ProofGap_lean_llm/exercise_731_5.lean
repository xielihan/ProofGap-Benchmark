import Mathlib

open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace Exercise731_5

def RationalSet : Set ℝ := {x | ∃ q : ℚ, (q : ℝ) = x}
def IntegerSet : Set ℝ := {x | ∃ k : ℤ, (k : ℝ) = x}

-- A side oscillates when it has neither a finite limit nor either infinite limit.
def OscillatesAlong (f : ℝ → ℝ) (l : Filter ℝ) : Prop :=
  (¬ ∃ L : ℝ, Tendsto f l (𝓝 L)) ∧
  ¬ Tendsto f l atTop ∧ ¬ Tendsto f l atBot

-- 振荡奇点: at least one one-sided limit fails even in the extended sense.
def OscillatorySingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop :=
  OscillatesAlong f (𝓝[<] a) ∨ OscillatesAlong f (𝓝[>] a)

end Exercise731_5
open Exercise731_5

/- Exercise 731_5, gap 1
SHA-256: 470e47ac7507d62ba9a418b53f6fc9f5c207b98315c5cb31752dc6b689565d57
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ sin(π * x) if x ∈ RationalSet; 0 if x ∈ RealSet ∧ x ∉ RationalSet }

GOAL:
forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ sin(π * a) ≠ 0

METHOD:

-/
theorem proof_gap_exercise_731_5_1
  (f : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∈ RationalSet then Real.sin (Real.pi * x) else 0)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet → Real.sin (Real.pi * a) ≠ 0 := by
  sorry

/- Exercise 731_5, gap 2
SHA-256: 3310d77288fe2d025522d402052c85146c81410f281a05eea51986fda473a79b
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ sin(π * x) if x ∈ RationalSet; 0 if x ∈ RealSet ∧ x ∉ RationalSet }
3. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ sin(π * a) ≠ 0

GOAL:
forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ RationalSet ∧ |x - a| < ε ∧ f(x) = sin(π * x)))

METHOD:

-/
theorem proof_gap_exercise_731_5_2
  (f : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∈ RationalSet then Real.sin (Real.pi * x) else 0)
  (h3 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet → Real.sin (Real.pi * a) ≠ 0)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ RationalSet ∧
        |x - a| < ε ∧ f x = Real.sin (Real.pi * x) := by
  sorry

/- Exercise 731_5, gap 3
SHA-256: 10772c069ce3bc2e271da714894715c471348bc3a50f335f54b255fb782e549b
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ sin(π * x) if x ∈ RationalSet; 0 if x ∈ RealSet ∧ x ∉ RationalSet }
3. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ sin(π * a) ≠ 0
4. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ RationalSet ∧ |x - a| < ε ∧ f(x) = sin(π * x)))

GOAL:
forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∉ RationalSet ∧ |x - a| < ε ∧ f(x) = 0))

METHOD:

-/
theorem proof_gap_exercise_731_5_3
  (f : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∈ RationalSet then Real.sin (Real.pi * x) else 0)
  (h3 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet → Real.sin (Real.pi * a) ≠ 0)
  (h4 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ RationalSet ∧
        |x - a| < ε ∧ f x = Real.sin (Real.pi * x))
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ RationalSet ∧
        |x - a| < ε ∧ f x = 0 := by
  sorry

/- Exercise 731_5, gap 4
SHA-256: a4e35d4b47cd46e8a38b2b8fbfd14604bc63b5234fe80c50ed1e94c765d91126
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ sin(π * x) if x ∈ RationalSet; 0 if x ∈ RealSet ∧ x ∉ RationalSet }
3. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ sin(π * a) ≠ 0
4. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ RationalSet ∧ |x - a| < ε ∧ f(x) = sin(π * x)))
5. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∉ RationalSet ∧ |x - a| < ε ∧ f(x) = 0))

GOAL:
forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ ¬(exists (L), L ∈ RealSet ∧ lim_{ x → a } (f(x)) = L)

METHOD:

-/
theorem proof_gap_exercise_731_5_4
  (f : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∈ RationalSet then Real.sin (Real.pi * x) else 0)
  (h3 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet → Real.sin (Real.pi * a) ≠ 0)
  (h4 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ RationalSet ∧
        |x - a| < ε ∧ f x = Real.sin (Real.pi * x))
  (h5 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ RationalSet ∧
        |x - a| < ε ∧ f x = 0)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ¬ (∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ Tendsto f (𝓝[≠] a) (𝓝 L)) := by
  sorry

/- Exercise 731_5, gap 5
SHA-256: 8f289c41ab3a83f26872f978899f85bf9bad6f6786f470770793446d86414ec8
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ sin(π * x) if x ∈ RationalSet; 0 if x ∈ RealSet ∧ x ∉ RationalSet }
3. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ sin(π * a) ≠ 0
4. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ RationalSet ∧ |x - a| < ε ∧ f(x) = sin(π * x)))
5. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∉ RationalSet ∧ |x - a| < ε ∧ f(x) = 0))
6. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ ¬(exists (L), L ∈ RealSet ∧ lim_{ x → a } (f(x)) = L)

GOAL:
forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ OscillatorySingularPoint(f, a)

METHOD:

-/
theorem proof_gap_exercise_731_5_5
  (f : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∈ RationalSet then Real.sin (Real.pi * x) else 0)
  (h3 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet → Real.sin (Real.pi * a) ≠ 0)
  (h4 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ RationalSet ∧
        |x - a| < ε ∧ f x = Real.sin (Real.pi * x))
  (h5 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ RationalSet ∧
        |x - a| < ε ∧ f x = 0)
  (h6 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ¬ (∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ Tendsto f (𝓝[≠] a) (𝓝 L)))
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    OscillatorySingularPoint f a := by
  sorry

/- Exercise 731_5, gap 6
SHA-256: b315de618a3bb3c97daf8097b16d89994e8178ddeddf10d0142c2e0cb4cfbd17
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ sin(π * x) if x ∈ RationalSet; 0 if x ∈ RealSet ∧ x ∉ RationalSet }
3. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ sin(π * a) ≠ 0
4. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ RationalSet ∧ |x - a| < ε ∧ f(x) = sin(π * x)))
5. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∉ RationalSet ∧ |x - a| < ε ∧ f(x) = 0))
6. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ ¬(exists (L), L ∈ RealSet ∧ lim_{ x → a } (f(x)) = L)
7. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ OscillatorySingularPoint(f, a)

GOAL:
forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ OscillatorySingularPoint(f, a)

METHOD:

-/
theorem proof_gap_exercise_731_5_6
  (f : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∈ RationalSet then Real.sin (Real.pi * x) else 0)
  (h3 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet → Real.sin (Real.pi * a) ≠ 0)
  (h4 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ RationalSet ∧
        |x - a| < ε ∧ f x = Real.sin (Real.pi * x))
  (h5 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ RationalSet ∧
        |x - a| < ε ∧ f x = 0)
  (h6 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ¬ (∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ Tendsto f (𝓝[≠] a) (𝓝 L)))
  (h7 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    OscillatorySingularPoint f a)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    OscillatorySingularPoint f a := by
  sorry

/- Exercise 731_5, gap 7
SHA-256: da114ecf072c3c217ea6b152c919e92eca02d0efa7940106745471cf42dad485
PROOF GAP @7
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ sin(π * x) if x ∈ RationalSet; 0 if x ∈ RealSet ∧ x ∉ RationalSet }
3. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ sin(π * a) ≠ 0
4. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ RationalSet ∧ |x - a| < ε ∧ f(x) = sin(π * x)))
5. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∉ RationalSet ∧ |x - a| < ε ∧ f(x) = 0))
6. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ ¬(exists (L), L ∈ RealSet ∧ lim_{ x → a } (f(x)) = L)
7. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ OscillatorySingularPoint(f, a)
8. forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ OscillatorySingularPoint(f, a)

GOAL:
forall (a), a ∈ RealSet ∧ a ∉ IntegerSet ⇒ OscillatorySingularPoint(f, a)

METHOD:

-/
theorem proof_gap_exercise_731_5_7
  (f : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∈ RationalSet then Real.sin (Real.pi * x) else 0)
  (h3 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet → Real.sin (Real.pi * a) ≠ 0)
  (h4 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ RationalSet ∧
        |x - a| < ε ∧ f x = Real.sin (Real.pi * x))
  (h5 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ RationalSet ∧
        |x - a| < ε ∧ f x = 0)
  (h6 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    ¬ (∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ Tendsto f (𝓝[≠] a) (𝓝 L)))
  (h7 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    OscillatorySingularPoint f a)
  (h8 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    OscillatorySingularPoint f a)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) ∧ a ∉ IntegerSet →
    OscillatorySingularPoint f a := by
  sorry

