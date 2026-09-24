import Mathlib

open Filter
open scoped Topology

namespace Exercise407_9

-- A real-valued function is represented by its domain D and an ambient value map f.
-- Only values on D are mathematical data; the extension outside D is immaterial.
def Defined (D : Set ℝ) (s : Set ℝ) : Prop := s ⊆ D

def LimitAtInfinity (f : ℝ → ℝ) (D : Set ℝ) (b : ℝ) : Prop :=
  Tendsto f (atTop ⊓ Filter.principal D) (𝓝 b)

def BelowCondition (f : ℝ → ℝ) (D : Set ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℝ, N > 0 ∧
    ∀ x : ℝ, x > N ∧ x ∈ D → 0 < b - f x ∧ b - f x < ε

-- Equality with the restricted lambda includes equality of domains and values.
def RestrictedReciprocal (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  D = Set.Ioi 0 ∧ ∀ x : ℝ, x ∈ D → f x = -(1 / x)

-- Exercise 407_9, gap 1
-- SHA-256: dbd483031c7d54c0f5d85fc1675c58a5387cefe5439e2d587b266000b6460cf3
/-
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. Defined(f, (a, +∞))

GOAL:
lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x > N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))

METHOD:

-/
-- Source issue: ordinary convergence does not imply eventual strict approach from below.
theorem proof_gap_exercise_407_9_1
  (f : ℝ → ℝ) (D : Set ℝ) (a b : ℝ)
  (h4 : Defined D (Set.Ioi a))
  : LimitAtInfinity f D b ↔ BelowCondition f D b := by
  sorry

-- Exercise 407_9, gap 2
-- SHA-256: c7c78c1ff6c067788ceca1370080f4b73c7f56e1cfad714a8d4b854a4c52f786
/-
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. Defined(f, (a, +∞))
5. lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x > N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
6. f = (fun x [x ∈ RealSet ∧ x > 0] . -frac(1, x))
7. a = 0
8. b = 0

GOAL:
Defined(f, (0, +∞))

METHOD:

-/
theorem proof_gap_exercise_407_9_2
  (f : ℝ → ℝ) (D : Set ℝ) (a b : ℝ)
  (h4 : Defined D (Set.Ioi a))
  (h5 : LimitAtInfinity f D b ↔ BelowCondition f D b)
  (h6 : RestrictedReciprocal f D)
  (h7 : a = 0)
  (h8 : b = 0)
  : Defined D (Set.Ioi 0) := by
  sorry

-- Exercise 407_9, gap 3
-- SHA-256: 0a2b9276a136b6d914fb935e3dc22c384c03c047ac503b953ceb1a8d9ab1d42d
/-
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. Defined(f, (a, +∞))
5. lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x > N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
6. f = (fun x [x ∈ RealSet ∧ x > 0] . -frac(1, x))
7. a = 0
8. b = 0
9. Defined(f, (0, +∞))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x > N ∧ x ∈ Dom(f) ⇒ 0 < 0 - f(x) ∧ 0 - f(x) < ε))

METHOD:

-/
theorem proof_gap_exercise_407_9_3
  (f : ℝ → ℝ) (D : Set ℝ) (a b : ℝ)
  (h4 : Defined D (Set.Ioi a))
  (h5 : LimitAtInfinity f D b ↔ BelowCondition f D b)
  (h6 : RestrictedReciprocal f D)
  (h7 : a = 0)
  (h8 : b = 0)
  (h9 : Defined D (Set.Ioi 0))
  : BelowCondition f D 0 := by
  sorry

-- Exercise 407_9, gap 4
-- SHA-256: 6b8fe467ab63de39ee61f26b344cdeb8648acd8de2046c30109b9e41391d61f3
/-
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. Defined(f, (a, +∞))
5. lim_{ x → +∞ } (f(x)) = b ⇔ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x > N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))
6. f = (fun x [x ∈ RealSet ∧ x > 0] . -frac(1, x))
7. a = 0
8. b = 0
9. Defined(f, (0, +∞))
10. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x > N ∧ x ∈ Dom(f) ⇒ 0 < 0 - f(x) ∧ 0 - f(x) < ε))

GOAL:
forall (x), x ∈ RealSet ∧ x > 0 ∧ f(x) = -frac(1, x) ∧ a = 0 ∧ b = 0 ⇒ lim_{ x → +∞ } (f(x)) = b ∧ (forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (N), N ∈ RealSet ∧ N > 0 ∧ (forall (x), x ∈ RealSet ∧ x > N ∧ x ∈ Dom(f) ⇒ 0 < b - f(x) ∧ b - f(x) < ε)))

METHOD:

-/
theorem proof_gap_exercise_407_9_4
  (f : ℝ → ℝ) (D : Set ℝ) (a b : ℝ)
  (h4 : Defined D (Set.Ioi a))
  (h5 : LimitAtInfinity f D b ↔ BelowCondition f D b)
  (h6 : RestrictedReciprocal f D)
  (h7 : a = 0)
  (h8 : b = 0)
  (h9 : Defined D (Set.Ioi 0))
  (h10 : BelowCondition f D 0)
  : ∀ x : ℝ, x > 0 ∧ f x = -(1 / x) ∧ a = 0 ∧ b = 0 →
      LimitAtInfinity f D b ∧ BelowCondition f D b := by
  sorry

end Exercise407_9
