import Mathlib

open Filter
open scoped Topology

namespace Exercise40710

-- The original text specifies |x| → +∞, encompassing both real tails.
def infinity : Filter ℝ := Filter.comap (fun x : ℝ => |x|) atTop

def upperTail (y : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
    ∃ N : ℝ, N ∈ (Set.univ : Set ℝ) ∧ N > 0 ∧
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ |x| > N →
        0 < y x - b ∧ y x - b < ε

-- b + 0 denotes convergence strictly from above, not addition of zero.
def fromAbove (y : ℝ → ℝ) (b : ℝ) : Prop :=
  Tendsto y infinity (nhdsWithin b (Set.Ioi b))

-- Preserve the source's function-versus-scalar equality, without inserting
-- the application present in RNFL but missing from the actual gap.
def malformedEquality : Prop :=
  ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    HEq (fun t : ℝ => 1 / |t|) (1 / |x|)

end Exercise40710

open Exercise40710

/- Exercise 407_10, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. b ∈ RealSet
4. y = f
5. lim_{ x → ∞ } (y(x)) = b
6. forall (x), x ∈ RealSet ⇒ y(x) > b
GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < y(x) - b ∧ y(x) - b < ε))

METHOD:

-/
theorem proof_gap_exercise_407_10_1
  (y f : ℝ → ℝ) (b : ℝ)
  (hb : b ∈ (Set.univ : Set ℝ)) (hyf : y = f)
  (hlim : Tendsto y infinity (𝓝 b))
  (hpos : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x > b)
  : upperTail y b := by
  sorry

/- Exercise 407_10, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. b ∈ RealSet
4. y = f
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < y(x) - b ∧ y(x) - b < ε))

GOAL:
lim_{ x → ∞ } (y(x)) = b + 0

METHOD:

-/
theorem proof_gap_exercise_407_10_2
  (y f : ℝ → ℝ) (b : ℝ)
  (hb : b ∈ (Set.univ : Set ℝ)) (hyf : y = f)
  (htail : upperTail y b)
  : fromAbove y b := by
  sorry

/- Exercise 407_10, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. b ∈ RealSet
4. y = f
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < y(x) - b ∧ y(x) - b < ε))
6. lim_{ x → ∞ } (y(x)) = b + 0

GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ (fun x [x ∈ RealSet] . frac(1, |x|)) = frac(1, |x|)

METHOD:

-/
theorem proof_gap_exercise_407_10_3
  (y f : ℝ → ℝ) (b : ℝ)
  (hb : b ∈ (Set.univ : Set ℝ)) (hyf : y = f)
  (htail : upperTail y b)
  (hlim : fromAbove y b)
  : malformedEquality := by
  sorry

/- Exercise 407_10, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. b ∈ RealSet
4. y = f
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < y(x) - b ∧ y(x) - b < ε))
6. lim_{ x → ∞ } (y(x)) = b + 0
7. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ (fun x [x ∈ RealSet] . frac(1, |x|)) = frac(1, |x|)

GOAL:
lim_{ x → ∞ } (fun x [x ∈ RealSet] . frac(1, |x|)) = 0 + 0

METHOD:

-/
theorem proof_gap_exercise_407_10_4
  (y f : ℝ → ℝ) (b : ℝ)
  (hb : b ∈ (Set.univ : Set ℝ)) (hyf : y = f)
  (htail : upperTail y b)
  (hlim : fromAbove y b)
  (hbad : malformedEquality)
  : fromAbove (fun x : ℝ => 1 / |x|) 0 := by
  sorry

