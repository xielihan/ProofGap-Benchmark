import Mathlib

open Filter
open scoped Topology

-- A removable discontinuity of the total real function supplied in the gaps.
-- Its domain is all of ℝ, so membership in the closure of the domain is automatic.
def exercise692RemovableSingularPoint (y : ℝ → ℝ) (a : ℝ) : Prop :=
  ¬ ContinuousAt y a ∧ ∃ L : ℝ, Tendsto y (𝓝[≠] a) (𝓝 L)

/- Exercise 692, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ |4 - x^{2}| ≠ 0 ∧ frac(1 - cos(π * x), |4 - x^{2}|) ≥ 0 ⇒ y(x) = sqrtn(2, frac(1 - cos(π * x), |4 - x^{2}|))
GOAL:
lim_{ x → 2 } (y(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_692_1
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |4 - x ^ 2| ≠ 0 ∧
    (1 - Real.cos (Real.pi * x)) / |4 - x ^ 2| ≥ 0 →
    y x = Real.sqrt ((1 - Real.cos (Real.pi * x)) / |4 - x ^ 2|))
  : Tendsto y (𝓝[≠] (2 : ℝ)) (𝓝 0) := by
  sorry

/- Exercise 692, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ |4 - x^{2}| ≠ 0 ∧ frac(1 - cos(π * x), |4 - x^{2}|) ≥ 0 ⇒ y(x) = sqrtn(2, frac(1 - cos(π * x), |4 - x^{2}|))
4. lim_{ x → 2 } (y(x)) = 0
GOAL:
lim_{ x → -2 } (y(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_692_2
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |4 - x ^ 2| ≠ 0 ∧
    (1 - Real.cos (Real.pi * x)) / |4 - x ^ 2| ≥ 0 →
    y x = Real.sqrt ((1 - Real.cos (Real.pi * x)) / |4 - x ^ 2|))
  (hpos : Tendsto y (𝓝[≠] (2 : ℝ)) (𝓝 0))
  : Tendsto y (𝓝[≠] (-2 : ℝ)) (𝓝 0) := by
  sorry

/- Exercise 692, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ 4 - x^{2} ≠ 0 ∧ frac(1 - cos(π * x), 4 - x^{2}) ≥ 0 ⇒ y(x) = sqrtn(2, frac(1 - cos(π * x), 4 - x^{2}))
4. lim_{ x → 2 } (y(x)) = 0
5. lim_{ x → -2 } (y(x)) = 0

GOAL:
RemovableSingularPoint(y, 2)

METHOD:

-/
theorem proof_gap_exercise_692_3
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (4 - x ^ 2) ≠ 0 ∧
    (1 - Real.cos (Real.pi * x)) / (4 - x ^ 2) ≥ 0 →
    y x = Real.sqrt ((1 - Real.cos (Real.pi * x)) / (4 - x ^ 2)))
  (hpos : Tendsto y (𝓝[≠] (2 : ℝ)) (𝓝 0))
  (hneg : Tendsto y (𝓝[≠] (-2 : ℝ)) (𝓝 0))
  : exercise692RemovableSingularPoint y 2 := by
  sorry

/- Exercise 692, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ 4 - x^{2} ≠ 0 ∧ frac(1 - cos(π * x), 4 - x^{2}) ≥ 0 ⇒ y(x) = sqrtn(2, frac(1 - cos(π * x), 4 - x^{2}))
4. lim_{ x → 2 } (y(x)) = 0
5. lim_{ x → -2 } (y(x)) = 0
6. RemovableSingularPoint(y, 2)

GOAL:
RemovableSingularPoint(y, -2)

METHOD:

-/
theorem proof_gap_exercise_692_4
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (4 - x ^ 2) ≠ 0 ∧
    (1 - Real.cos (Real.pi * x)) / (4 - x ^ 2) ≥ 0 →
    y x = Real.sqrt ((1 - Real.cos (Real.pi * x)) / (4 - x ^ 2)))
  (hpos : Tendsto y (𝓝[≠] (2 : ℝ)) (𝓝 0))
  (hneg : Tendsto y (𝓝[≠] (-2 : ℝ)) (𝓝 0))
  (hrpos : exercise692RemovableSingularPoint y 2)
  : exercise692RemovableSingularPoint y (-2) := by
  sorry

/- Exercise 692, gap 5
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ |4 - x^{2}| ≠ 0 ∧ frac(1 - cos(π * x), |4 - x^{2}|) ≥ 0 ⇒ y(x) = sqrtn(2, frac(1 - cos(π * x), |4 - x^{2}|))
4. lim_{ x → 2 } (y(x)) = 0
5. lim_{ x → -2 } (y(x)) = 0
6. RemovableSingularPoint(y, 2)
7. RemovableSingularPoint(y, -2)
GOAL:
a ∈ { 2, -2 } ⇔ ¬ContinuousFuncAt(y, a)

METHOD:

-/
theorem proof_gap_exercise_692_5
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |4 - x ^ 2| ≠ 0 ∧
    (1 - Real.cos (Real.pi * x)) / |4 - x ^ 2| ≥ 0 →
    y x = Real.sqrt ((1 - Real.cos (Real.pi * x)) / |4 - x ^ 2|))
  (hpos : Tendsto y (𝓝[≠] (2 : ℝ)) (𝓝 0))
  (hneg : Tendsto y (𝓝[≠] (-2 : ℝ)) (𝓝 0))
  (hrpos : exercise692RemovableSingularPoint y 2)
  (hrneg : exercise692RemovableSingularPoint y (-2))
  : a ∈ ({2, -2} : Set ℝ) ↔ ¬ ContinuousAt y a := by
  sorry

