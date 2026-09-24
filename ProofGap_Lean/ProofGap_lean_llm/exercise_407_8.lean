import Mathlib

open Filter
open scoped Topology

namespace Exercise407_8

-- A real-valued function with an explicit domain; values outside dom are unused.
structure DomainFunction where
  dom : Set ℝ
  value : ℝ → ℝ

def Defined (f : DomainFunction) (s : Set ℝ) : Prop := s ⊆ f.dom

def LimitAtNegInf (f : DomainFunction) (b : ℝ) : Prop :=
  Tendsto f.value (atBot ⊓ Filter.principal f.dom) (𝓝 b)

def BelowCriterion (f : DomainFunction) (b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℝ, N > 0 ∧
    ∀ x : ℝ, x < -N ∧ x ∈ f.dom → 0 < b - f.value x ∧ b - f.value x < ε

-- Equality to the restricted lambda means equal domains and equal values on that domain.
def IsRestrictedReciprocal (f : DomainFunction) : Prop :=
  f.dom = Set.Iio 0 ∧ ∀ x : ℝ, x < 0 → f.value x = 1 / x

end Exercise407_8

open Exercise407_8

/- Exercise 407_8, gap 1
SHA-256: 76dcda251fd6738064bb0a001d0f0f4c2e6b198d8584af1ddd23c41200f12514
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. Defined(f, (-∞, a))

GOAL:
lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))

METHOD:

-/
theorem proof_gap_exercise_407_8_1
  (f : DomainFunction) (a b : ℝ)
  (h4 : Defined f (Set.Iio a))
  : LimitAtNegInf f b ↔ BelowCriterion f b := by
  sorry

/- Exercise 407_8, gap 2
SHA-256: 23f00ca5b695301136d449063cf40bdcc33f632c6404fd5cf5226d1ef698d748
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. Defined(f, (-∞, a))
5. lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
6. f = (fun x [x ∈ RealSet ∧ x < 0] . frac(1, x))
7. a = 0
8. b = 0

GOAL:
Defined(f, (-∞, 0))

METHOD:

-/
theorem proof_gap_exercise_407_8_2
  (f : DomainFunction) (a b : ℝ)
  (h4 : Defined f (Set.Iio a))
  (h5 : LimitAtNegInf f b ↔ BelowCriterion f b)
  (h6 : IsRestrictedReciprocal f)
  (h7 : a = 0) (h8 : b = 0)
  : Defined f (Set.Iio 0) := by
  sorry

/- Exercise 407_8, gap 3
SHA-256: 14fac88ffd83863690cdfd85aaf41127eb90a3ea64eeb25003ed1ea0c49a641d
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. Defined(f, (-∞, a))
5. lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
6. f = (fun x [x ∈ RealSet ∧ x < 0] . frac(1, x))
7. a = 0
8. b = 0
9. Defined(f, (-∞, 0))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ∧ x ∈ Dom(f) ⇒ 0 < 0 - f(x) ∧ 0 - f(x) < ε))

METHOD:

-/
theorem proof_gap_exercise_407_8_3
  (f : DomainFunction) (a b : ℝ)
  (h4 : Defined f (Set.Iio a))
  (h5 : LimitAtNegInf f b ↔ BelowCriterion f b)
  (h6 : IsRestrictedReciprocal f)
  (h7 : a = 0) (h8 : b = 0)
  (h9 : Defined f (Set.Iio 0))
  : BelowCriterion f 0 := by
  sorry

/- Exercise 407_8, gap 4
SHA-256: 3bdbbf0cced09558ff30913be41abdd806930341f349dcd439833a2fa7a6cf0c
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. Defined(f, (-∞, a))
5. lim_{ x → -∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
6. f = (fun x [x ∈ RealSet ∧ x < 0] . frac(1, x))
7. a = 0
8. b = 0
9. Defined(f, (-∞, 0))
10. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ∧ x ∈ Dom(f) ⇒ 0 < 0 - f(x) ∧ 0 - f(x) < ε))

GOAL:
forall (x), x ∈ RealSet ∧ x < 0 ∧ f(x) = frac(1, x) ∧ a = 0 ∧ b = 0 ⇒ lim_{ x → -∞ } (f(x)) = b ∧ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x < -N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))

METHOD:

-/
theorem proof_gap_exercise_407_8_4
  (f : DomainFunction) (a b : ℝ)
  (h4 : Defined f (Set.Iio a))
  (h5 : LimitAtNegInf f b ↔ BelowCriterion f b)
  (h6 : IsRestrictedReciprocal f)
  (h7 : a = 0) (h8 : b = 0)
  (h9 : Defined f (Set.Iio 0))
  (h10 : BelowCriterion f 0)
  : ∀ x : ℝ, x < 0 ∧ f.value x = 1 / x ∧ a = 0 ∧ b = 0 →
      LimitAtNegInf f b ∧ BelowCriterion f b := by
  sorry

