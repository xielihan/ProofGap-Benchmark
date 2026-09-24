import Mathlib

open Filter
open scoped Topology

namespace Exercise690

-- Unsigned infinity in the source means divergence in absolute value.
def UnsignedInfiniteLimit (y : ℝ → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun x => |y x|) (𝓝[≠] c) atTop

-- A real infinite discontinuity has an infinite limit on at least one side.
-- Absolute value includes either sign of infinity.
def InfiniteSingularPoint (y : ℝ → ℝ) (c : ℝ) : Prop :=
  ¬ ContinuousAt y c ∧
    (Tendsto (fun x => |y x|) (𝓝[<] c) atTop ∨
     Tendsto (fun x => |y x|) (𝓝[>] c) atTop)

-- For the total function in the gaps, a removable discontinuity requires
-- discontinuity as well as a finite punctured limit.
def RemovableSingularPoint (y : ℝ → ℝ) (c : ℝ) : Prop :=
  ¬ ContinuousAt y c ∧ ∃ L : ℝ, Tendsto y (𝓝[≠] c) (𝓝 L)

end Exercise690

open Exercise690

/- Exercise 690, gap 1
SHA-256: a94d810800d23714877bf11240de26bcb5b2775fec2d1f2f72de31a230df2698
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ⇒ y(x) = frac(frac(1, x) - frac(1, x + 1), frac(1, x - 1) - frac(1, x))

GOAL:
lim_{ x → -1 } (y(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_690_1
  (y : ℝ → ℝ) (a : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 →
    y x = (1 / x - 1 / (x + 1)) / (1 / (x - 1) - 1 / x))
  : UnsignedInfiniteLimit y (-1) := by
  sorry

/- Exercise 690, gap 2
SHA-256: 3f414b8025485eec9191d34f1cbbd35267398af4f09152c57f09fa8584fb5a8d
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ⇒ y(x) = frac(frac(1, x) - frac(1, x + 1), frac(1, x - 1) - frac(1, x))
4. lim_{ x → -1 } (y(x)) = ∞

GOAL:
lim_{ x → 0 } (y(x)) = -1

METHOD:

-/
theorem proof_gap_exercise_690_2
  (y : ℝ → ℝ) (a : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 →
    y x = (1 / x - 1 / (x + 1)) / (1 / (x - 1) - 1 / x))
  (h4 : UnsignedInfiniteLimit y (-1))
  : Tendsto y (𝓝[≠] 0) (𝓝 (-1)) := by
  sorry

/- Exercise 690, gap 3
SHA-256: 74128da77b7a1c6a19df0f10a51a8671719343371b5ac887f89b69a7cdc760ec
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ⇒ y(x) = frac(frac(1, x) - frac(1, x + 1), frac(1, x - 1) - frac(1, x))
4. lim_{ x → -1 } (y(x)) = ∞
5. lim_{ x → 0 } (y(x)) = -1

GOAL:
lim_{ x → 1 } (y(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_690_3
  (y : ℝ → ℝ) (a : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 →
    y x = (1 / x - 1 / (x + 1)) / (1 / (x - 1) - 1 / x))
  (h4 : UnsignedInfiniteLimit y (-1))
  (h5 : Tendsto y (𝓝[≠] 0) (𝓝 (-1)))
  : Tendsto y (𝓝[≠] 1) (𝓝 0) := by
  sorry

/- Exercise 690, gap 4
SHA-256: ae544b94b3dcfdd918ea752d6314cb684bbdb1cf1aee5ef5893e2704d68c67d1
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ⇒ y(x) = frac(frac(1, x) - frac(1, x + 1), frac(1, x - 1) - frac(1, x))
4. lim_{ x → -1 } (y(x)) = ∞
5. lim_{ x → 0 } (y(x)) = -1
6. lim_{ x → 1 } (y(x)) = 0

GOAL:
InfiniteSingularPoint(y, -1)

METHOD:

-/
theorem proof_gap_exercise_690_4
  (y : ℝ → ℝ) (a : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 →
    y x = (1 / x - 1 / (x + 1)) / (1 / (x - 1) - 1 / x))
  (h4 : UnsignedInfiniteLimit y (-1))
  (h5 : Tendsto y (𝓝[≠] 0) (𝓝 (-1)))
  (h6 : Tendsto y (𝓝[≠] 1) (𝓝 0))
  : InfiniteSingularPoint y (-1) := by
  sorry

/- Exercise 690, gap 5
SHA-256: a9957aa824e12ddd8a24c29d7a0b65a735e51d21a0ee8342b4e1815dbf39ca98
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ⇒ y(x) = frac(frac(1, x) - frac(1, x + 1), frac(1, x - 1) - frac(1, x))
4. lim_{ x → (-1)^- } (y(x)) = +∞ ∧ lim_{ x → (-1)^+ } (y(x)) = -∞
5. lim_{ x → 0 } (y(x)) = -1
6. lim_{ x → 1 } (y(x)) = 0
7. InfiniteSingularPoint(y, -1)
GOAL:
RemovableSingularPoint(y, 0)

METHOD:

-/
theorem proof_gap_exercise_690_5
  (y : ℝ → ℝ) (a : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 →
    y x = (1 / x - 1 / (x + 1)) / (1 / (x - 1) - 1 / x))
  (h4 : Tendsto y (𝓝[<] (-1)) atTop ∧ Tendsto y (𝓝[>] (-1)) atBot)
  (h5 : Tendsto y (𝓝[≠] 0) (𝓝 (-1)))
  (h6 : Tendsto y (𝓝[≠] 1) (𝓝 0))
  (h7 : InfiniteSingularPoint y (-1))
  : RemovableSingularPoint y 0 := by
  sorry

/- Exercise 690, gap 6
SHA-256: 0fa045fe0447ba24b0a59cb7bce1c02a262dd8e1b821b9d78d908239504653cf
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ⇒ y(x) = frac(frac(1, x) - frac(1, x + 1), frac(1, x - 1) - frac(1, x))
4. lim_{ x → (-1)^- } (y(x)) = +∞ ∧ lim_{ x → (-1)^+ } (y(x)) = -∞
5. lim_{ x → 0 } (y(x)) = -1
6. lim_{ x → 1 } (y(x)) = 0
7. InfiniteSingularPoint(y, -1)
8. RemovableSingularPoint(y, 0)
GOAL:
RemovableSingularPoint(y, 1)

METHOD:

-/
theorem proof_gap_exercise_690_6
  (y : ℝ → ℝ) (a : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 →
    y x = (1 / x - 1 / (x + 1)) / (1 / (x - 1) - 1 / x))
  (h4 : Tendsto y (𝓝[<] (-1)) atTop ∧ Tendsto y (𝓝[>] (-1)) atBot)
  (h5 : Tendsto y (𝓝[≠] 0) (𝓝 (-1)))
  (h6 : Tendsto y (𝓝[≠] 1) (𝓝 0))
  (h7 : InfiniteSingularPoint y (-1))
  (h8 : RemovableSingularPoint y 0)
  : RemovableSingularPoint y 1 := by
  sorry

/- Exercise 690, gap 7
SHA-256: 8c9ed378e4b4edc455c5b0d23826f1b56fccb04d65d236b44a385dd2dc26d59d
PROOF GAP @7
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ⇒ y(x) = frac(frac(1, x) - frac(1, x + 1), frac(1, x - 1) - frac(1, x))
4. lim_{ x → -1 } (y(x)) = ∞
5. lim_{ x → 0 } (y(x)) = -1
6. lim_{ x → 1 } (y(x)) = 0
7. InfiniteSingularPoint(y, -1)
8. RemovableSingularPoint(y, 0)
9. RemovableSingularPoint(y, 1)

GOAL:
a ∈ { -1, 0, 1 } ⇔ ¬ContinuousFuncAt(y, a)

METHOD:

-/
theorem proof_gap_exercise_690_7
  (y : ℝ → ℝ) (a : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 →
    y x = (1 / x - 1 / (x + 1)) / (1 / (x - 1) - 1 / x))
  (h4 : UnsignedInfiniteLimit y (-1))
  (h5 : Tendsto y (𝓝[≠] 0) (𝓝 (-1)))
  (h6 : Tendsto y (𝓝[≠] 1) (𝓝 0))
  (h7 : InfiniteSingularPoint y (-1))
  (h8 : RemovableSingularPoint y 0)
  (h9 : RemovableSingularPoint y 1)
  : a ∈ ({-1, 0, 1} : Set ℝ) ↔ ¬ ContinuousAt y a := by
  sorry

