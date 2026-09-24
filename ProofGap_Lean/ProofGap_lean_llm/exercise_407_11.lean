import Mathlib

open Filter
open scoped Topology

-- b + 0 denotes approach strictly from above, not real addition.
namespace Exercise407_11

def AboveTail (y : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
    ∃ N : ℝ, N ∈ (Set.univ : Set ℝ) ∧ N > 0 ∧
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x < -N →
        0 < y x - b ∧ y x - b < ε

-- The RNFL explicitly applies this lambda to the outer x. The FNFL/gap
-- printer dropped that application. Restore the source RNFL application;
-- retain the exact printed gaps below and document this source defect in review.
def ExamplePointwiseIdentity : Prop :=
  ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    (fun t : ℝ => -(1 / t)) x = -(1 / x)

end Exercise407_11

open Exercise407_11

/- Exercise 407_11, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. b ∈ RealSet
4. y = f
5. lim_{ x → -∞ } (y(x)) = b
6. forall (x), x ∈ RealSet ⇒ y(x) > b
GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ⇒ 0 < y(x) - b ∧ y(x) - b < ε))

METHOD:

-/
theorem proof_gap_exercise_407_11_1
  (y f : ℝ → ℝ) (b : ℝ)
  (hb : b ∈ (Set.univ : Set ℝ))
  (hyf : y = f)
  (hlim : Tendsto y atBot (𝓝 b))
  (habove : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x > b)
  : AboveTail y b := by
  sorry

/- Exercise 407_11, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. b ∈ RealSet
4. y = f
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ⇒ 0 < y(x) - b ∧ y(x) - b < ε))

GOAL:
lim_{ x → -∞ } (y(x)) = b + 0

METHOD:

-/
theorem proof_gap_exercise_407_11_2
  (y f : ℝ → ℝ) (b : ℝ)
  (hb : b ∈ (Set.univ : Set ℝ))
  (hyf : y = f)
  (htail : AboveTail y b)
  : Tendsto y atBot (𝓝[>] b) := by
  sorry

/- Exercise 407_11, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. b ∈ RealSet
4. y = f
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ⇒ 0 < y(x) - b ∧ y(x) - b < ε))
6. lim_{ x → -∞ } (y(x)) = b + 0

GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ (fun x [x ∈ RealSet] . -frac(1, x)) = -frac(1, x)

METHOD:

-/
theorem proof_gap_exercise_407_11_3
  (y f : ℝ → ℝ) (b : ℝ)
  (hb : b ∈ (Set.univ : Set ℝ))
  (hyf : y = f)
  (htail : AboveTail y b)
  (hlim : Tendsto y atBot (𝓝[>] b))
  : ExamplePointwiseIdentity := by
  sorry

/- Exercise 407_11, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. b ∈ RealSet
4. y = f
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ⇒ 0 < y(x) - b ∧ y(x) - b < ε))
6. lim_{ x → -∞ } (y(x)) = b + 0
7. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ (fun x [x ∈ RealSet] . -frac(1, x)) = -frac(1, x)

GOAL:
lim_{ x → -∞ } (fun x [x ∈ RealSet] . -frac(1, x)) = 0 + 0

METHOD:

-/
theorem proof_gap_exercise_407_11_4
  (y f : ℝ → ℝ) (b : ℝ)
  (hb : b ∈ (Set.univ : Set ℝ))
  (hyf : y = f)
  (htail : AboveTail y b)
  (hlim : Tendsto y atBot (𝓝[>] b))
  (hsource : ExamplePointwiseIdentity)
  : Tendsto (fun x : ℝ => -(1 / x)) atBot (𝓝[>] (0 : ℝ)) := by
  sorry

