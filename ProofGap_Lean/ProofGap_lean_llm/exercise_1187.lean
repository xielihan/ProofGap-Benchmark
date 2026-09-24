import Mathlib

open scoped BigOperators

-- Literal repository definition, the theorem library, Thm 285.
-- Its inclusive bound is retained (see the semantic review).
def exercise1187ClassK (f : ℝ → ℝ) (k : ℕ) : Prop :=
  (∀ j : ℕ, j ≤ k → Differentiable ℝ (iteratedDeriv j f)) ∧
    Continuous (iteratedDeriv k f)

-- Scalar a and coefficient sequence c are distinct, as in the original exercise.
-- range (n + 1 - d) represents 0 ≤ i ≤ n-d with ordinary integer bounds.
-- In particular the second-derivative sum is empty when n = 1.

/- Exercise 1187, gap 1
SHA-256: bffec3d7bc7878a719aaf8bb73fbf285079cb8bd2eec69491b22f9a19065e5a9
PROOF GAP @1
ASSUM:
1. P : RealSet → RealSet
2. y : RealSet → RealSet
3. n ∈ NonNegIntegerSet
4. a ∈ RealSet
5. b ∈ RealSet
6. a_{0} ∈ RealSet
7. i ∈ NonNegIntegerSet
8. n ∈ PosIntegerSet
9. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ n ⇒ a(i) ∈ RealSet
10. forall (x), x ∈ RealSet ⇒ P(x) = sum_{ i = 0 }^{ n } (a(i) * x^{n - i})
11. forall (x), x ∈ RealSet ⇒ y(x) = P(a * x + b)

GOAL:
forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 1)(x) = sum_{ i = 0 }^{ n - 1 } (a(i) * (n - i) * x^{n - i - 1})

METHOD:

-/
theorem proof_gap_exercise_1187_1
  (P y : ℝ → ℝ) (n : ℕ) (a b : ℝ)
  (a₀ : ℝ) -- Standalone a_{0} declaration in the gap, retained without a new equation.
  (c : ℕ → ℝ) (i : ℕ)
  (hn : 0 < n)
  (hc : ∀ j : ℕ, j ≤ n → c j ∈ (Set.univ : Set ℝ))
  (hP : ∀ x : ℝ, P x = ∑ j ∈ Finset.range (n + 1), c j * x ^ (n - j))
  (hy : ∀ x : ℝ, y x = P (a * x + b))
  : ∀ x : ℝ, iteratedDeriv 1 P x = ∑ j ∈ Finset.range n, c j * (n - j : ℝ) * x ^ (n - j - 1) := by
  sorry

/- Exercise 1187, gap 2
SHA-256: 7e48257aa8410a85d2ae68044a7a7432e6b97730182dda162995cf80d7123c42
PROOF GAP @2
ASSUM:
1. P : RealSet → RealSet
2. y : RealSet → RealSet
3. n ∈ NonNegIntegerSet
4. a ∈ RealSet
5. b ∈ RealSet
6. a_{0} ∈ RealSet
7. i ∈ NonNegIntegerSet
8. n ∈ PosIntegerSet
9. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ n ⇒ a(i) ∈ RealSet
10. forall (x), x ∈ RealSet ⇒ P(x) = sum_{ i = 0 }^{ n } (a(i) * x^{n - i})
11. forall (x), x ∈ RealSet ⇒ y(x) = P(a * x + b)
12. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 1)(x) = sum_{ i = 0 }^{ n - 1 } (a(i) * (n - i) * x^{n - i - 1})

GOAL:
forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 2)(x) = sum_{ i = 0 }^{ n - 2 } (a(i) * (n - i) * (n - i - 1) * x^{n - i - 2})

METHOD:

-/
theorem proof_gap_exercise_1187_2
  (P y : ℝ → ℝ) (n : ℕ) (a b : ℝ)
  (a₀ : ℝ) -- Standalone a_{0} declaration in the gap, retained without a new equation.
  (c : ℕ → ℝ) (i : ℕ)
  (hn : 0 < n)
  (hc : ∀ j : ℕ, j ≤ n → c j ∈ (Set.univ : Set ℝ))
  (hP : ∀ x : ℝ, P x = ∑ j ∈ Finset.range (n + 1), c j * x ^ (n - j))
  (hy : ∀ x : ℝ, y x = P (a * x + b))
  (hD1 : ∀ x : ℝ, iteratedDeriv 1 P x = ∑ j ∈ Finset.range n, c j * (n - j : ℝ) * x ^ (n - j - 1))
  : ∀ x : ℝ, iteratedDeriv 2 P x = ∑ j ∈ Finset.range (n - 1), c j * (n - j : ℝ) * (n - j - 1 : ℝ) * x ^ (n - j - 2) := by
  sorry

/- Exercise 1187, gap 3
SHA-256: a01d18f3abc78642845b71b9aeaed586d6113f93a4255be2a3d036a9e61a95c3
PROOF GAP @3
ASSUM:
1. P : RealSet → RealSet
2. y : RealSet → RealSet
3. n ∈ NonNegIntegerSet
4. a ∈ RealSet
5. b ∈ RealSet
6. a_{0} ∈ RealSet
7. i ∈ NonNegIntegerSet
8. n ∈ PosIntegerSet
9. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ n ⇒ a(i) ∈ RealSet
10. forall (x), x ∈ RealSet ⇒ P(x) = sum_{ i = 0 }^{ n } (a(i) * x^{n - i})
11. forall (x), x ∈ RealSet ⇒ y(x) = P(a * x + b)
12. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 1)(x) = sum_{ i = 0 }^{ n - 1 } (a(i) * (n - i) * x^{n - i - 1})
13. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 2)(x) = sum_{ i = 0 }^{ n - 2 } (a(i) * (n - i) * (n - i - 1) * x^{n - i - 2})

GOAL:
forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, n)(x) = n! * a(0)

METHOD:

-/
theorem proof_gap_exercise_1187_3
  (P y : ℝ → ℝ) (n : ℕ) (a b : ℝ)
  (a₀ : ℝ) -- Standalone a_{0} declaration in the gap, retained without a new equation.
  (c : ℕ → ℝ) (i : ℕ)
  (hn : 0 < n)
  (hc : ∀ j : ℕ, j ≤ n → c j ∈ (Set.univ : Set ℝ))
  (hP : ∀ x : ℝ, P x = ∑ j ∈ Finset.range (n + 1), c j * x ^ (n - j))
  (hy : ∀ x : ℝ, y x = P (a * x + b))
  (hD1 : ∀ x : ℝ, iteratedDeriv 1 P x = ∑ j ∈ Finset.range n, c j * (n - j : ℝ) * x ^ (n - j - 1))
  (hD2 : ∀ x : ℝ, iteratedDeriv 2 P x = ∑ j ∈ Finset.range (n - 1), c j * (n - j : ℝ) * (n - j - 1 : ℝ) * x ^ (n - j - 2))
  : ∀ x : ℝ, iteratedDeriv n P x = (n.factorial : ℝ) * c 0 := by
  sorry

/- Exercise 1187, gap 4
SHA-256: f727e859cf39f324d82442ba96ff49c2c6816231575c8a76efe66ee6dc96d7c0
PROOF GAP @4
ASSUM:
1. P : RealSet → RealSet
2. y : RealSet → RealSet
3. n ∈ NonNegIntegerSet
4. a ∈ RealSet
5. b ∈ RealSet
6. c : NonNegIntegerSet → RealSet
7. i ∈ NonNegIntegerSet
8. n ∈ PosIntegerSet
9. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ n ⇒ c(i) ∈ RealSet
10. forall (x), x ∈ RealSet ⇒ P(x) = sum_{ i = 0 }^{ n } (c(i) * x^{n - i})
11. forall (x), x ∈ RealSet ⇒ y(x) = P(a * x + b)
12. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 1)(x) = sum_{ i = 0 }^{ n - 1 } (c(i) * (n - i) * x^{n - i - 1})
13. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 2)(x) = sum_{ i = 0 }^{ n - 2 } (c(i) * (n - i) * (n - i - 1) * x^{n - i - 2})
14. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, n)(x) = n! * c(0)
15. FuncOfClassK(P, n)
16. FuncOfClassK(y, n)
GOAL:
forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = a^{n} * FunDeri(P, 1, n)(a * x + b)

METHOD:

-/
theorem proof_gap_exercise_1187_4
  (P y : ℝ → ℝ) (n : ℕ) (a b : ℝ)
  (c : ℕ → ℝ) (i : ℕ)
  (hn : 0 < n)
  (hc : ∀ j : ℕ, j ≤ n → c j ∈ (Set.univ : Set ℝ))
  (hP : ∀ x : ℝ, P x = ∑ j ∈ Finset.range (n + 1), c j * x ^ (n - j))
  (hy : ∀ x : ℝ, y x = P (a * x + b))
  (hD1 : ∀ x : ℝ, iteratedDeriv 1 P x = ∑ j ∈ Finset.range n, c j * (n - j : ℝ) * x ^ (n - j - 1))
  (hD2 : ∀ x : ℝ, iteratedDeriv 2 P x = ∑ j ∈ Finset.range (n - 1), c j * (n - j : ℝ) * (n - j - 1 : ℝ) * x ^ (n - j - 2))
  (hDn : ∀ x : ℝ, iteratedDeriv n P x = (n.factorial : ℝ) * c 0)
  (hclassP : exercise1187ClassK P n)
  (hclassY : exercise1187ClassK y n)
  : ∀ x : ℝ, iteratedDeriv n y x = a ^ n * iteratedDeriv n P (a * x + b) := by
  sorry

/- Exercise 1187, gap 5
SHA-256: 2c1aa28f88db919082b6911182e7131349a5b238ffdd6ae094391d28ba6b6dec
PROOF GAP @5
ASSUM:
1. P : RealSet → RealSet
2. y : RealSet → RealSet
3. n ∈ NonNegIntegerSet
4. a ∈ RealSet
5. b ∈ RealSet
6. a_{0} ∈ RealSet
7. i ∈ NonNegIntegerSet
8. n ∈ PosIntegerSet
9. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ n ⇒ a(i) ∈ RealSet
10. forall (x), x ∈ RealSet ⇒ P(x) = sum_{ i = 0 }^{ n } (a(i) * x^{n - i})
11. forall (x), x ∈ RealSet ⇒ y(x) = P(a * x + b)
12. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 1)(x) = sum_{ i = 0 }^{ n - 1 } (a(i) * (n - i) * x^{n - i - 1})
13. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, 2)(x) = sum_{ i = 0 }^{ n - 2 } (a(i) * (n - i) * (n - i - 1) * x^{n - i - 2})
14. forall (x), x ∈ RealSet ⇒ FunDeri(P, 1, n)(x) = n! * a(0)
15. forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = a^{n} * FunDeri(P, 1, n)(a * x + b)

GOAL:
forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = n! * a(0) * a^{n}

METHOD:

-/
theorem proof_gap_exercise_1187_5
  (P y : ℝ → ℝ) (n : ℕ) (a b : ℝ)
  (a₀ : ℝ) -- Standalone a_{0} declaration in the gap, retained without a new equation.
  (c : ℕ → ℝ) (i : ℕ)
  (hn : 0 < n)
  (hc : ∀ j : ℕ, j ≤ n → c j ∈ (Set.univ : Set ℝ))
  (hP : ∀ x : ℝ, P x = ∑ j ∈ Finset.range (n + 1), c j * x ^ (n - j))
  (hy : ∀ x : ℝ, y x = P (a * x + b))
  (hD1 : ∀ x : ℝ, iteratedDeriv 1 P x = ∑ j ∈ Finset.range n, c j * (n - j : ℝ) * x ^ (n - j - 1))
  (hD2 : ∀ x : ℝ, iteratedDeriv 2 P x = ∑ j ∈ Finset.range (n - 1), c j * (n - j : ℝ) * (n - j - 1 : ℝ) * x ^ (n - j - 2))
  (hDn : ∀ x : ℝ, iteratedDeriv n P x = (n.factorial : ℝ) * c 0)
  (hchain : ∀ x : ℝ, iteratedDeriv n y x = a ^ n * iteratedDeriv n P (a * x + b))
  : ∀ x : ℝ, iteratedDeriv n y x = (n.factorial : ℝ) * c 0 * a ^ n := by
  sorry

