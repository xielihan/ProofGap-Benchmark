import Mathlib

-- Graph of a function whose domain is precisely ImageOn(y, RealSet).
def exercise760Graph (y : ℝ → ℝ) (x : Set.range y → ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ u : Set.range y, (u : ℝ) = p.1 ∧ x u = p.2}

-- InverseFunc is the reversed graph, per predicate explanation Thm 221.
def exercise760InverseGraph (y : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | y p.2 = p.1}

/- Exercise 760, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. x : RealSet → RealSet
3. forall (t), t ∈ RealSet ⇒ y(t) = t + floor(t)

GOAL:
forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)

METHOD:

-/
theorem proof_gap_exercise_760_1
  (y : ℝ → ℝ)
  (x : ℝ → ℝ)
  (h3 : ∀ (t : ℝ), y t = t + (⌊t⌋ : ℤ))
  : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → ⌊t⌋ = k := by
  sorry

/- Exercise 760, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. x : RealSet → RealSet
3. forall (t), t ∈ RealSet ⇒ y(t) = t + floor(t)
4. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)

GOAL:
forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) = t + k)

METHOD:

-/
theorem proof_gap_exercise_760_2
  (y : ℝ → ℝ)
  (x : ℝ → ℝ)
  (h3 : ∀ (t : ℝ), y t = t + (⌊t⌋ : ℤ))
  (h4 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → ⌊t⌋ = k)
  : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t = t + (k : ℝ) := by
  sorry

/- Exercise 760, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. x : RealSet → RealSet
3. forall (t), t ∈ RealSet ⇒ y(t) = t + floor(t)
4. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)
5. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) = t + k)

GOAL:
forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ 2 * k ≤ y(t))

METHOD:

-/
theorem proof_gap_exercise_760_3
  (y : ℝ → ℝ)
  (x : ℝ → ℝ)
  (h3 : ∀ (t : ℝ), y t = t + (⌊t⌋ : ℤ))
  (h4 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → ⌊t⌋ = k)
  (h5 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t = t + (k : ℝ))
  : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → 2 * (k : ℝ) ≤ y t := by
  sorry

/- Exercise 760, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. x : RealSet → RealSet
3. forall (t), t ∈ RealSet ⇒ y(t) = t + floor(t)
4. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)
5. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) = t + k)
6. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ 2 * k ≤ y(t))

GOAL:
forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) < 2 * k + 1)

METHOD:

-/
theorem proof_gap_exercise_760_4
  (y : ℝ → ℝ)
  (x : ℝ → ℝ)
  (h3 : ∀ (t : ℝ), y t = t + (⌊t⌋ : ℤ))
  (h4 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → ⌊t⌋ = k)
  (h5 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t = t + (k : ℝ))
  (h6 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → 2 * (k : ℝ) ≤ y t)
  : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t < 2 * (k : ℝ) + 1 := by
  sorry

/- Exercise 760, gap 5
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. x : RealSet → RealSet
3. forall (t), t ∈ RealSet ⇒ y(t) = t + floor(t)
4. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)
5. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) = t + k)
6. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ 2 * k ≤ y(t))
7. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) < 2 * k + 1)

GOAL:
forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ t = y(t) - k)

METHOD:

-/
theorem proof_gap_exercise_760_5
  (y : ℝ → ℝ)
  (x : ℝ → ℝ)
  (h3 : ∀ (t : ℝ), y t = t + (⌊t⌋ : ℤ))
  (h4 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → ⌊t⌋ = k)
  (h5 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t = t + (k : ℝ))
  (h6 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → 2 * (k : ℝ) ≤ y t)
  (h7 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t < 2 * (k : ℝ) + 1)
  : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → t = y t - (k : ℝ) := by
  sorry

/- Exercise 760, gap 6
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. x : RealSet → RealSet
3. forall (t), t ∈ RealSet ⇒ y(t) = t + floor(t)
4. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)
5. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) = t + k)
6. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ 2 * k ≤ y(t))
7. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) < 2 * k + 1)
8. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ t = y(t) - k)

GOAL:
forall (s) (k), s ∈ RealSet ∧ k ∈ IntegerSet ∧ 2 * k ≤ s ∧ s < 2 * k + 1 ⇒ x(s) = s - k

METHOD:

-/
theorem proof_gap_exercise_760_6
  (y : ℝ → ℝ)
  (x : ℝ → ℝ)
  (h3 : ∀ (t : ℝ), y t = t + (⌊t⌋ : ℤ))
  (h4 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → ⌊t⌋ = k)
  (h5 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t = t + (k : ℝ))
  (h6 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → 2 * (k : ℝ) ≤ y t)
  (h7 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t < 2 * (k : ℝ) + 1)
  (h8 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → t = y t - (k : ℝ))
  : ∀ (s : ℝ) (k : ℤ), 2 * (k : ℝ) ≤ s ∧ s < 2 * (k : ℝ) + 1 → x s = s - (k : ℝ) := by
  sorry

/- Exercise 760, gap 7
PROOF GAP @7
ASSUM:
1. y : RealSet → RealSet
2. x : ImageOn(y, RealSet) → RealSet
3. forall (t), t ∈ RealSet ⇒ y(t) = t + floor(t)
4. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)
5. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) = t + k)
6. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ 2 * k ≤ y(t))
7. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ y(t) < 2 * k + 1)
8. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ IntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ t = y(t) - k)
9. forall (s) (k), s ∈ RealSet ∧ k ∈ IntegerSet ∧ 2 * k ≤ s ∧ s < 2 * k + 1 ⇒ x(s) = s - k
GOAL:
(forall (s) (k), s ∈ RealSet ∧ k ∈ IntegerSet ∧ 2 * k ≤ s ∧ s < 2 * k + 1 ⇒ x(s) = s - k) ⇒ InverseFunc(y) = x

METHOD:

-/
theorem proof_gap_exercise_760_7
  (y : ℝ → ℝ)
  (x : Set.range y → ℝ)
  (h3 : ∀ (t : ℝ), y t = t + (⌊t⌋ : ℤ))
  (h4 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → ⌊t⌋ = k)
  (h5 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t = t + (k : ℝ))
  (h6 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → 2 * (k : ℝ) ≤ y t)
  (h7 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → y t < 2 * (k : ℝ) + 1)
  (h8 : ∀ (t : ℝ) (k : ℤ), (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 → t = y t - (k : ℝ))
  (h9 : ∀ (s : ℝ) (k : ℤ), 2 * (k : ℝ) ≤ s ∧ s < 2 * (k : ℝ) + 1 → (s, s - (k : ℝ)) ∈ exercise760Graph y x)
  : (∀ (s : ℝ) (k : ℤ), 2 * (k : ℝ) ≤ s ∧ s < 2 * (k : ℝ) + 1 → (s, s - (k : ℝ)) ∈ exercise760Graph y x) → exercise760InverseGraph y = exercise760Graph y x := by
  sorry

