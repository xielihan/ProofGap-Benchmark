import Mathlib

namespace Exercise759

-- InverseFunc is the converse graph, as in the theorem library, Thm 221.
def graph (y : ℝ → ℝ) : Set (ℝ × ℝ) := {p | y p.1 = p.2}
def inverseGraph (y : ℝ → ℝ) : Set (ℝ × ℝ) := {p | y p.2 = p.1}

-- An inverse value is defined and unique: its fiber is exactly the singleton {v}.
-- This avoids choosing an arbitrary preimage when y is not bijective.
def inverseValue (y : ℝ → ℝ) (x v : ℝ) : Prop :=
  ∀ t : ℝ, y t = x ↔ t = v

/- Exercise 759, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet
5. d ∈ RealSet
6. a * d - b * c ≠ 0
7. forall (x), x ∈ RealSet ∧ c * x + d ≠ 0 ⇒ y(x) = frac(a * x + b, c * x + d)
8. c ≠ 0 ⇒ y(frac(-d, c)) = frac(a, c)
GOAL:
forall (x), x ∈ RealSet ∧ c * x - a ≠ 0 ⇒ InverseFunc(y, x) = frac(-d * x + b, c * x - a)

METHOD:

-/
theorem proof_gap_exercise_759_1
  (y : ℝ → ℝ) (a b c d : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hc : c ∈ (Set.univ : Set ℝ))
  (hd : d ∈ (Set.univ : Set ℝ))
  (hdet : a * d - b * c ≠ 0)
  (hformula : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x + d ≠ 0 →
    y x = (a * x + b) / (c * x + d))
  (hpole : c ≠ 0 → y (-d / c) = a / c)
  : (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x - a ≠ 0 →
    inverseValue y x ((-d * x + b) / (c * x - a))) := by
  sorry

/- Exercise 759, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet
5. d ∈ RealSet
6. a * d - b * c ≠ 0
7. forall (x), x ∈ RealSet ∧ c * x + d ≠ 0 ⇒ y(x) = frac(a * x + b, c * x + d)
8. forall (x), x ∈ RealSet ∧ c * x - a ≠ 0 ⇒ InverseFunc(y, x) = frac(-d * x + b, c * x - a)

GOAL:
forall (x), x ∈ RealSet ∧ c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧ frac(a * x + b, c * x + d) = frac(-x * d + b, x * c - a) ⇒ InverseFunc(y) = y

METHOD:

-/
theorem proof_gap_exercise_759_2
  (y : ℝ → ℝ) (a b c d : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hc : c ∈ (Set.univ : Set ℝ))
  (hd : d ∈ (Set.univ : Set ℝ))
  (hdet : a * d - b * c ≠ 0)
  (hformula : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x + d ≠ 0 →
    y x = (a * x + b) / (c * x + d))
  (hinverse : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x - a ≠ 0 →
    inverseValue y x ((-d * x + b) / (c * x - a)))
  : (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧
    (a * x + b) / (c * x + d) = (-x * d + b) / (x * c - a) →
    inverseGraph y = graph y) := by
  sorry

/- Exercise 759, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet
5. d ∈ RealSet
6. a * d - b * c ≠ 0
7. forall (x), x ∈ RealSet ∧ c * x + d ≠ 0 ⇒ y(x) = frac(a * x + b, c * x + d)
8. forall (x), x ∈ RealSet ∧ c * x - a ≠ 0 ⇒ InverseFunc(y, x) = frac(-d * x + b, c * x - a)
9. forall (x), x ∈ RealSet ∧ c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧ frac(a * x + b, c * x + d) = frac(-x * d + b, x * c - a) ⇒ InverseFunc(y) = y

GOAL:
forall (x), x ∈ RealSet ∧ a + d = 0 ⇒ c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧ frac(a * x + b, c * x + d) = frac(-x * d + b, x * c - a)

METHOD:

-/
theorem proof_gap_exercise_759_3
  (y : ℝ → ℝ) (a b c d : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hc : c ∈ (Set.univ : Set ℝ))
  (hd : d ∈ (Set.univ : Set ℝ))
  (hdet : a * d - b * c ≠ 0)
  (hformula : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x + d ≠ 0 →
    y x = (a * x + b) / (c * x + d))
  (hinverse : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x - a ≠ 0 →
    inverseValue y x ((-d * x + b) / (c * x - a)))
  (hpoint : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧
    (a * x + b) / (c * x + d) = (-x * d + b) / (x * c - a) →
    inverseGraph y = graph y)
  : (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ a + d = 0 →
    c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧
    (a * x + b) / (c * x + d) = (-x * d + b) / (x * c - a)) := by
  sorry

/- Exercise 759, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet
5. d ∈ RealSet
6. a * d - b * c ≠ 0
7. forall (x), x ∈ RealSet ∧ c * x + d ≠ 0 ⇒ y(x) = frac(a * x + b, c * x + d)
8. forall (x), x ∈ RealSet ∧ c * x - a ≠ 0 ⇒ InverseFunc(y, x) = frac(-d * x + b, c * x - a)
9. c ≠ 0 ⇒ y(frac(-d, c)) = frac(a, c)
GOAL:
a + d = 0 ⇒ InverseFunc(y) = y

METHOD:

-/
theorem proof_gap_exercise_759_4
  (y : ℝ → ℝ) (a b c d : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hc : c ∈ (Set.univ : Set ℝ))
  (hd : d ∈ (Set.univ : Set ℝ))
  (hdet : a * d - b * c ≠ 0)
  (hformula : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x + d ≠ 0 →
    y x = (a * x + b) / (c * x + d))
  (hpole : c ≠ 0 → y (-d / c) = a / c)
  (hinverse : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x - a ≠ 0 →
    inverseValue y x ((-d * x + b) / (c * x - a)))
  : (a + d = 0 → inverseGraph y = graph y) := by
  sorry

/- Exercise 759, gap 5
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet
5. d ∈ RealSet
6. a * d - b * c ≠ 0
7. forall (x), x ∈ RealSet ∧ c * x + d ≠ 0 ⇒ y(x) = frac(a * x + b, c * x + d)
8. forall (x), x ∈ RealSet ∧ c * x - a ≠ 0 ⇒ InverseFunc(y, x) = frac(-d * x + b, c * x - a)
9. forall (x), x ∈ RealSet ∧ c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧ frac(a * x + b, c * x + d) = frac(-x * d + b, x * c - a) ⇒ InverseFunc(y) = y
10. forall (x), x ∈ RealSet ∧ a + d = 0 ⇒ c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧ frac(a * x + b, c * x + d) = frac(-x * d + b, x * c - a)
11. a + d = 0 ⇒ InverseFunc(y) = y

GOAL:
(a, b, c, d) ∈ { (a, b, c, d) | a ∈ RealSet ∧ b ∈ RealSet ∧ c ∈ RealSet ∧ d ∈ RealSet, a * d - b * c ≠ 0, a + d = 0 } ⇔ InverseFunc(y) = y

METHOD:

-/
theorem proof_gap_exercise_759_5
  (y : ℝ → ℝ) (a b c d : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hb : b ∈ (Set.univ : Set ℝ))
  (hc : c ∈ (Set.univ : Set ℝ))
  (hd : d ∈ (Set.univ : Set ℝ))
  (hdet : a * d - b * c ≠ 0)
  (hformula : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x + d ≠ 0 →
    y x = (a * x + b) / (c * x + d))
  (hinverse : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x - a ≠ 0 →
    inverseValue y x ((-d * x + b) / (c * x - a)))
  (hpoint : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧
    (a * x + b) / (c * x + d) = (-x * d + b) / (x * c - a) →
    inverseGraph y = graph y)
  (htrace : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ a + d = 0 →
    c * x + d ≠ 0 ∧ c * x - a ≠ 0 ∧
    (a * x + b) / (c * x + d) = (-x * d + b) / (x * c - a))
  (hsuff : a + d = 0 → inverseGraph y = graph y)
  : ((a, b, c, d) ∈ {p : ℝ × ℝ × ℝ × ℝ |
      p.1 ∈ (Set.univ : Set ℝ) ∧ p.2.1 ∈ (Set.univ : Set ℝ) ∧
      p.2.2.1 ∈ (Set.univ : Set ℝ) ∧ p.2.2.2 ∈ (Set.univ : Set ℝ) ∧
      p.1 * p.2.2.2 - p.2.1 * p.2.2.1 ≠ 0 ∧ p.1 + p.2.2.2 = 0} ↔
    inverseGraph y = graph y) := by
  sorry

end Exercise759
