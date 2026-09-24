import Mathlib

open Filter
open scoped Topology

namespace Exercise404

-- A real-valued function is represented by its domain D and a total extension f.
-- All limit filters are restricted to D; values outside D do not affect limits.
def limBoth (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ) : Prop :=
  Tendsto f ((Filter.comap (fun x : ℝ => |x|) atTop) ⊓ Filter.principal D) (𝓝 b)

def limNeg (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ) : Prop :=
  Tendsto f (atBot ⊓ Filter.principal D) (𝓝 b)

def limPos (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ) : Prop :=
  Tendsto f (atTop ⊓ Filter.principal D) (𝓝 b)

def epsBoth (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℝ, N > 0 ∧
    ∀ x : ℝ, x ∈ D ∧ |x| > N → |f x - b| < ε

def epsNeg (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℝ, N > 0 ∧
    ∀ x : ℝ, x ∈ D ∧ x < -N → |f x - b| < ε

def epsPos (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℝ, N > 0 ∧
    ∀ x : ℝ, x ∈ D ∧ x > N → |f x - b| < ε

-- Equality with the restricted lambda means equality of domains and values there.
def isRestrictedInvSquare (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  D = {x : ℝ | x ≠ 0} ∧ ∀ x : ℝ, x ≠ 0 → f x = 1 / x ^ (2 : ℕ)

end Exercise404

open Exercise404

/- Exercise 404, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet

GOAL:
lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x| > N ⇒ |f(x) - b| < ε)))

METHOD:

-/
theorem proof_gap_exercise_404_1
  (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ)
  : (limBoth D f b ↔ epsBoth D f b) := by
  sorry

/- Exercise 404, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x > N ⇒ |f(x) - b| < ε)))

GOAL:
lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x < -N ⇒ |f(x) - b| < ε)))

METHOD:

-/
theorem proof_gap_exercise_404_2
  (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ)
  (h3 : limBoth D f b ↔ epsPos D f b)
  : (limNeg D f b ↔ epsNeg D f b) := by
  sorry

/- Exercise 404, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x > N ⇒ |f(x) - b| < ε)))
4. lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x < -N ⇒ |f(x) - b| < ε)))

GOAL:
lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x > N ⇒ |f(x) - b| < ε)))

METHOD:

-/
theorem proof_gap_exercise_404_3
  (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ)
  (h3 : limBoth D f b ↔ epsPos D f b)
  (h4 : limNeg D f b ↔ epsNeg D f b)
  : (limPos D f b ↔ epsPos D f b) := by
  sorry

/- Exercise 404, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x| > N ⇒ |f(x) - b| < ε)))
4. lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x < -N ⇒ |f(x) - b| < ε)))
5. lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x > N ⇒ |f(x) - b| < ε)))
6. f = (fun x [x ∈ RealSet ∧ x ≠ 0] . frac(1, x^{2}))
GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = frac(1, x^{2})

METHOD:

-/
theorem proof_gap_exercise_404_4
  (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ)
  (h3 : limBoth D f b ↔ epsBoth D f b)
  (h4 : limNeg D f b ↔ epsNeg D f b)
  (h5 : limPos D f b ↔ epsPos D f b)
  (h6 : isRestrictedInvSquare D f)
  : (∀ x : ℝ, x ≠ 0 → f x = 1 / x ^ (2 : ℕ)) := by
  sorry

/- Exercise 404, gap 5
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x| > N ⇒ |f(x) - b| < ε)))
4. lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x < -N ⇒ |f(x) - b| < ε)))
5. lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x > N ⇒ |f(x) - b| < ε)))
6. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = frac(1, x^{2})

GOAL:
lim_{ x → -∞ } (f(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_404_5
  (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ)
  (h3 : limBoth D f b ↔ epsBoth D f b)
  (h4 : limNeg D f b ↔ epsNeg D f b)
  (h5 : limPos D f b ↔ epsPos D f b)
  (h6 : ∀ x : ℝ, x ≠ 0 → f x = 1 / x ^ (2 : ℕ))
  : (limNeg D f 0) := by
  sorry

/- Exercise 404, gap 6
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x| > N ⇒ |f(x) - b| < ε)))
4. lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x < -N ⇒ |f(x) - b| < ε)))
5. lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x > N ⇒ |f(x) - b| < ε)))
6. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = frac(1, x^{2})
7. lim_{ x → -∞ } (f(x)) = 0

GOAL:
lim_{ x → +∞ } (f(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_404_6
  (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ)
  (h3 : limBoth D f b ↔ epsBoth D f b)
  (h4 : limNeg D f b ↔ epsNeg D f b)
  (h5 : limPos D f b ↔ epsPos D f b)
  (h6 : ∀ x : ℝ, x ≠ 0 → f x = 1 / x ^ (2 : ℕ))
  (h7 : limNeg D f 0)
  : (limPos D f 0) := by
  sorry

/- Exercise 404, gap 7
PROOF GAP @7
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x| > N ⇒ |f(x) - b| < ε)))
4. lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x < -N ⇒ |f(x) - b| < ε)))
5. lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ x > N ⇒ |f(x) - b| < ε)))
6. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = frac(1, x^{2})
7. lim_{ x → -∞ } (f(x)) = 0
8. lim_{ x → +∞ } (f(x)) = 0

GOAL:
lim_{ x → ∞ } (f(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_404_7
  (D : Set ℝ) (f : ℝ → ℝ) (b : ℝ)
  (h3 : limBoth D f b ↔ epsBoth D f b)
  (h4 : limNeg D f b ↔ epsNeg D f b)
  (h5 : limPos D f b ↔ epsPos D f b)
  (h6 : ∀ x : ℝ, x ≠ 0 → f x = 1 / x ^ (2 : ℕ))
  (h7 : limNeg D f 0)
  (h8 : limPos D f 0)
  : (limBoth D f 0) := by
  sorry

