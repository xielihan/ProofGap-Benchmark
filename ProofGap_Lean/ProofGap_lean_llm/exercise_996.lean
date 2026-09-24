import Mathlib

open scoped BigOperators

-- Integer indices are converted only under the source guard 1 ≤ k ≤ n.

/- Exercise 996, gap 1
PROOF GAP @1
ASSUM:
1. a : NonNegIntegerSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 0
3. f : RealSet → RealSet
4. n ∈ PosIntegerSet
5. forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ a(k) ∈ RealSet
6. f = (fun x [x ∈ RealSet] . sum_{ k = 1 }^{ n } (|x - a(k)|))
GOAL:
forall (x), x ∈ RealSet ⇒ f(x) = sum_{ k = 1 }^{ n } (|x - a(k)|)

METHOD:

-/
theorem proof_gap_exercise_996_1
  (a : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 0)
  (h4 : n ∈ {m : ℕ | 0 < m})
  (h5 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    a k.toNat ∈ (Set.univ : Set ℝ))
  (h6 : f = (fun x : ℝ => ∑ k ∈ Finset.Icc 1 n, |x - a k|))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = ∑ k ∈ Finset.Icc 1 n, |x - a k| := by
  sorry

/- Exercise 996, gap 2
PROOF GAP @2
ASSUM:
1. a : NonNegIntegerSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 0
3. f : RealSet → RealSet
4. n ∈ PosIntegerSet
5. forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ a(k) ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = sum_{ k = 1 }^{ n } (|x - a(k)|)

GOAL:
forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ ContinuousFuncAt(fun x [x ∈ RealSet] . |x - a(k)|, a(k)) ∧ ¬DiffableFuncAt(fun x [x ∈ RealSet] . |x - a(k)|, a(k))

METHOD:

-/
theorem proof_gap_exercise_996_2
  (a : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 0)
  (h4 : n ∈ {m : ℕ | 0 < m})
  (h5 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    a k.toNat ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = ∑ k ∈ Finset.Icc 1 n, |x - a k|)
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    ContinuousAt (fun x : ℝ => |x - a k.toNat|) (a k.toNat) ∧
      ¬ DifferentiableAt ℝ (fun x : ℝ => |x - a k.toNat|) (a k.toNat) := by
  sorry

/- Exercise 996, gap 3
PROOF GAP @3
ASSUM:
1. a : NonNegIntegerSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 0
3. f : RealSet → RealSet
4. n ∈ PosIntegerSet
5. forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ a(k) ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = sum_{ k = 1 }^{ n } (|x - a(k)|)
7. forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ ContinuousFuncAt(fun x [x ∈ RealSet] . |x - a(k)|, a(k)) ∧ ¬DiffableFuncAt(fun x [x ∈ RealSet] . |x - a(k)|, a(k))

GOAL:
forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ ContinuousFuncAt(f, a(k)) ∧ ¬DiffableFuncAt(f, a(k))

METHOD:

-/
theorem proof_gap_exercise_996_3
  (a : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 0)
  (h4 : n ∈ {m : ℕ | 0 < m})
  (h5 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    a k.toNat ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = ∑ k ∈ Finset.Icc 1 n, |x - a k|)
  (h7 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    ContinuousAt (fun x : ℝ => |x - a k.toNat|) (a k.toNat) ∧
      ¬ DifferentiableAt ℝ (fun x : ℝ => |x - a k.toNat|) (a k.toNat))
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    ContinuousAt f (a k.toNat) ∧ ¬ DifferentiableAt ℝ f (a k.toNat) := by
  sorry

/- Exercise 996, gap 4
PROOF GAP @4
ASSUM:
1. a : NonNegIntegerSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 0
3. f : RealSet → RealSet
4. n ∈ PosIntegerSet
5. forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ a(k) ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = sum_{ k = 1 }^{ n } (|x - a(k)|)
7. forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ ContinuousFuncAt(fun x [x ∈ RealSet] . |x - a(k)|, a(k)) ∧ ¬DiffableFuncAt(fun x [x ∈ RealSet] . |x - a(k)|, a(k))
8. forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ ContinuousFuncAt(f, a(k)) ∧ ¬DiffableFuncAt(f, a(k))

GOAL:
(forall (x), x ∈ RealSet ⇒ f(x) = sum_{ k = 1 }^{ n } (|x - a(k)|)) ⇒ (forall (k), k ∈ IntegerSet ∧ 1 ≤ k ∧ k ≤ n ⇒ ContinuousFuncAt(f, a(k)) ∧ ¬DiffableFuncAt(f, a(k)))

METHOD:

-/
theorem proof_gap_exercise_996_4
  (a : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 0)
  (h4 : n ∈ {m : ℕ | 0 < m})
  (h5 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    a k.toNat ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = ∑ k ∈ Finset.Icc 1 n, |x - a k|)
  (h7 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    ContinuousAt (fun x : ℝ => |x - a k.toNat|) (a k.toNat) ∧
      ¬ DifferentiableAt ℝ (fun x : ℝ => |x - a k.toNat|) (a k.toNat))
  (h8 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    ContinuousAt f (a k.toNat) ∧ ¬ DifferentiableAt ℝ f (a k.toNat))
  : (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = ∑ k ∈ Finset.Icc 1 n, |x - a k|) →
    (∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 1 ≤ k ∧ k ≤ (n : ℤ) →
    ContinuousAt f (a k.toNat) ∧ ¬ DifferentiableAt ℝ f (a k.toNat)) := by
  sorry
