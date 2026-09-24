import Mathlib

open scoped Topology
open Filter

namespace Exercise691

-- Unsigned infinity (∞, distinct from +∞): the absolute value tends to +∞.
def InfiniteLimit (y : ℝ → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun x => |y x|) (𝓝[≠] c) atTop

-- A removable discontinuity of the total real function used in the source gaps.
def RemovableSingularPoint (y : ℝ → ℝ) (c : ℝ) : Prop :=
  (¬ ContinuousAt y c) ∧ ∃ L : ℝ, Tendsto y (𝓝[≠] c) (𝓝 L)

-- An infinite discontinuity: at least one one-sided limit is unsigned infinity.
def InfiniteSingularPoint (y : ℝ → ℝ) (c : ℝ) : Prop :=
  (¬ ContinuousAt y c) ∧
    (Tendsto (fun x => |y x|) (𝓝[<] c) atTop ∨
     Tendsto (fun x => |y x|) (𝓝[>] c) atTop)

end Exercise691

open Exercise691

-- Exercise 691, gap 1
/-
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ sin(x) ≠ 0 ⇒ y(x) = frac(x, sin(x))

GOAL:
forall (k), k ∈ IntegerSet ⇒ sin(k * π) = 0

METHOD:

-/
theorem proof_gap_exercise_691_1
  (y : ℝ → ℝ)
  (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.sin x ≠ 0 →
    y x = x / Real.sin x)
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) → Real.sin ((k : ℝ) * Real.pi) = 0 := by
  sorry

-- Exercise 691, gap 2
/-
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ sin(x) ≠ 0 ⇒ y(x) = frac(x, sin(x))
4. forall (k), k ∈ IntegerSet ⇒ sin(k * π) = 0

GOAL:
lim_{ x → 0 } (y(x)) = 1

METHOD:

-/
theorem proof_gap_exercise_691_2
  (y : ℝ → ℝ)
  (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.sin x ≠ 0 →
    y x = x / Real.sin x)
  (hzeros : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) → Real.sin ((k : ℝ) * Real.pi) = 0)
  : Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  sorry

-- Exercise 691, gap 3
/-
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ sin(x) ≠ 0 ⇒ y(x) = frac(x, sin(x))
4. forall (k), k ∈ IntegerSet ⇒ sin(k * π) = 0
5. lim_{ x → 0 } (y(x)) = 1
6. y(0) ≠ 1
GOAL:
RemovableSingularPoint(y, 0)

METHOD:

-/
theorem proof_gap_exercise_691_3
  (y : ℝ → ℝ)
  (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.sin x ≠ 0 →
    y x = x / Real.sin x)
  (hzeros : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) → Real.sin ((k : ℝ) * Real.pi) = 0)
  (hlim0 : Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (hvalue0 : y 0 ≠ 1)
  : RemovableSingularPoint y 0 := by
  sorry

-- Exercise 691, gap 4
/-
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ sin(x) ≠ 0 ⇒ y(x) = frac(x, sin(x))
4. forall (k), k ∈ IntegerSet ⇒ sin(k * π) = 0
5. lim_{ x → 0 } (y(x)) = 1
6. RemovableSingularPoint(y, 0)

GOAL:
forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → k * π } (y(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_691_4
  (y : ℝ → ℝ)
  (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.sin x ≠ 0 →
    y x = x / Real.sin x)
  (hzeros : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) → Real.sin ((k : ℝ) * Real.pi) = 0)
  (hlim0 : Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (hremovable : RemovableSingularPoint y 0)
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    InfiniteLimit y ((k : ℝ) * Real.pi) := by
  sorry

-- Exercise 691, gap 5
/-
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ sin(x) ≠ 0 ⇒ y(x) = frac(x, sin(x))
4. forall (k), k ∈ IntegerSet ⇒ sin(k * π) = 0
5. lim_{ x → 0 } (y(x)) = 1
6. RemovableSingularPoint(y, 0)
7. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → k * π } (y(x)) = ∞

GOAL:
forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ InfiniteSingularPoint(y, k * π)

METHOD:

-/
theorem proof_gap_exercise_691_5
  (y : ℝ → ℝ)
  (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.sin x ≠ 0 →
    y x = x / Real.sin x)
  (hzeros : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) → Real.sin ((k : ℝ) * Real.pi) = 0)
  (hlim0 : Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (hremovable : RemovableSingularPoint y 0)
  (hinfinite : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    InfiniteLimit y ((k : ℝ) * Real.pi))
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    InfiniteSingularPoint y ((k : ℝ) * Real.pi) := by
  sorry

-- Exercise 691, gap 6
/-
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ sin(x) ≠ 0 ⇒ y(x) = frac(x, sin(x))
4. forall (k), k ∈ IntegerSet ⇒ sin(k * π) = 0
5. lim_{ x → 0 } (y(x)) = 1
6. RemovableSingularPoint(y, 0)
7. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → k * π } (y(x)) = ∞
8. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ InfiniteSingularPoint(y, k * π)

GOAL:
a ∈ { k * π | k ∈ IntegerSet } ⇔ ¬ContinuousFuncAt(y, a)

METHOD:

-/
theorem proof_gap_exercise_691_6
  (y : ℝ → ℝ)
  (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.sin x ≠ 0 →
    y x = x / Real.sin x)
  (hzeros : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) → Real.sin ((k : ℝ) * Real.pi) = 0)
  (hlim0 : Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (hremovable : RemovableSingularPoint y 0)
  (hinfinite : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    InfiniteLimit y ((k : ℝ) * Real.pi))
  (hsingular : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    InfiniteSingularPoint y ((k : ℝ) * Real.pi))
  : a ∈ Set.range (fun k : ℤ => (k : ℝ) * Real.pi) ↔ ¬ ContinuousAt y a := by
  sorry

