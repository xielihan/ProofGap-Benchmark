import Mathlib

open Filter
open scoped Topology

namespace Exercise407_7

-- Unsigned infinity means |x| tends to +infinity (both real tails).
def LimitAtInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  Tendsto f (Filter.comap (fun x : ℝ => |x|) atTop) (𝓝 b)

-- Existence of a real value on the indicated set; totality is already in f's type.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ y : ℝ, f x = y

def BelowCondition (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℝ, N > 0 ∧
    ∀ x : ℝ, |x| > N → 0 < b - f x ∧ b - f x < ε

-- Equality of the restricted functions, with no constraint on f 0.
def RestrictedExample (f : ℝ → ℝ) : Prop :=
  Set.EqOn f (fun x : ℝ => -(1 / |x|)) {x : ℝ | x ≠ 0}

end Exercise407_7

open Exercise407_7

/- Exercise 407_7, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. N_{0} ∈ RealSet
4. x ∈ RealSet
5. N_{0} > 0
6. Defined(f, { x | x ∈ RealSet, |x| > N_{0} })

GOAL:
lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))

METHOD:

-/
-- Source statement issue: ordinary convergence does not imply strict approach from below.
theorem proof_gap_exercise_407_7_1
  (f : ℝ → ℝ) (b N₀ x : ℝ)
  (h5 : N₀ > 0)
  (h6 : DefinedOn f {t : ℝ | |t| > N₀})
  : LimitAtInfinity f b ↔ BelowCondition f b := by
  sorry

/- Exercise 407_7, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. N_{0} ∈ RealSet
4. x ∈ RealSet
5. N_{0} > 0
6. Defined(f, { x | x ∈ RealSet, |x| > N_{0} })
7. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
8. f = (fun x [x ∈ RealSet ∧ x ≠ 0] . -frac(1, |x|))
9. b = 0

GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = -frac(1, |x|)

METHOD:

-/
theorem proof_gap_exercise_407_7_2
  (f : ℝ → ℝ) (b N₀ x : ℝ)
  (h5 : N₀ > 0)
  (h6 : DefinedOn f {t : ℝ | |t| > N₀})
  (h7 : LimitAtInfinity f b ↔ BelowCondition f b)
  (h8 : RestrictedExample f)
  (h9 : b = 0)
  : ∀ x : ℝ, x ≠ 0 → f x = -(1 / |x|) := by
  sorry

/- Exercise 407_7, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. N_{0} ∈ RealSet
4. x ∈ RealSet
5. N_{0} > 0
6. Defined(f, { x | x ∈ RealSet, |x| > N_{0} })
7. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
8. f = (fun x [x ∈ RealSet ∧ x ≠ 0] . -frac(1, |x|))
9. b = 0
10. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = -frac(1, |x|)

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < 0 - f(x) ∧ 0 - f(x) < ε))

METHOD:

-/
theorem proof_gap_exercise_407_7_3
  (f : ℝ → ℝ) (b N₀ x : ℝ)
  (h5 : N₀ > 0)
  (h6 : DefinedOn f {t : ℝ | |t| > N₀})
  (h7 : LimitAtInfinity f b ↔ BelowCondition f b)
  (h8 : RestrictedExample f)
  (h9 : b = 0)
  (h10 : ∀ x : ℝ, x ≠ 0 → f x = -(1 / |x|))
  : BelowCondition f 0 := by
  sorry

/- Exercise 407_7, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. b ∈ RealSet
3. N_{0} ∈ RealSet
4. x ∈ RealSet
5. N_{0} > 0
6. Defined(f, { x | x ∈ RealSet, |x| > N_{0} })
7. lim_{ x → ∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
8. f = (fun x [x ∈ RealSet ∧ x ≠ 0] . -frac(1, |x|))
9. b = 0
10. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = -frac(1, |x|)
11. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < 0 - f(x) ∧ 0 - f(x) < ε))

GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 0 ∧ f(x) = -frac(1, |x|) ∧ b = 0 ⇒ lim_{ x → ∞ } (f(x)) = b ∧ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ |x| > N ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))

METHOD:

-/
theorem proof_gap_exercise_407_7_4
  (f : ℝ → ℝ) (b N₀ x : ℝ)
  (h5 : N₀ > 0)
  (h6 : DefinedOn f {t : ℝ | |t| > N₀})
  (h7 : LimitAtInfinity f b ↔ BelowCondition f b)
  (h8 : RestrictedExample f)
  (h9 : b = 0)
  (h10 : ∀ x : ℝ, x ≠ 0 → f x = -(1 / |x|))
  (h11 : BelowCondition f 0)
  : ∀ x : ℝ, x ≠ 0 ∧ f x = -(1 / |x|) ∧ b = 0 →
      LimitAtInfinity f b ∧ BelowCondition f b := by
  sorry

