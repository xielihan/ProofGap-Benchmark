import Mathlib

open scoped BigOperators
set_option linter.unusedVariables false

namespace Exercise1230

-- Function-selector differentiation, iterated with the selector held fixed.
noncomputable def selectorDeriv (g : ℝ → ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | k + 1, f => fun t => deriv (selectorDeriv g k f) t / deriv g t

noncomputable def fd (f : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  selectorDeriv (fun t => t ^ 2) k f

-- Literal definition from the theorem library, Thm 285.
def classK (f : ℝ → ℝ) (k : ℕ) : Prop :=
  (∀ r : ℕ, r ≤ k → Differentiable ℝ (iteratedDeriv r f)) ∧
    Continuous (iteratedDeriv k f)

-- range (2*j) represents 0,...,2*j-1, including the empty product at j=0.
noncomputable def term (f : ℝ → ℝ) (n j : ℕ) (x : ℝ) : ℝ :=
  ((∏ i ∈ Finset.range (2 * j), ((n : ℝ) - (i : ℝ))) /
    (Nat.factorial j : ℝ)) * (2 * x) ^ ((n : ℤ) - 2 * (j : ℤ)) *
    fd f (n - j) (x ^ 2)

noncomputable def series (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 0 (n / 2), term f n j x

noncomputable def expanded (f : ℝ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  (2 * x) ^ (m + 1) * fd f (m + 1) (x ^ 2) +
  (((m : ℝ) + 1) * (m : ℝ) / (Nat.factorial 1 : ℝ)) *
    (2 * x) ^ ((m : ℤ) - 1) * fd f m (x ^ 2) +
  (((m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) /
    (Nat.factorial 2 : ℝ)) * (2 * x) ^ ((m : ℤ) - 3) *
    fd f (m - 1) (x ^ 2) +
  ∑ j ∈ Finset.Icc 3 ((m + 1) / 2), term f (m + 1) j x

def base (y f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : ℝ), n = 1 →
    iteratedDeriv 1 y x = 2 * x * fd f 1 (x ^ 2)

def baseSum (y f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : ℝ) (j i : ℕ), n = 1 →
    iteratedDeriv n y x = series f n x

def stepExpanded (y f : ℝ → ℝ) : Prop :=
  ∀ (m : ℕ) (x : ℝ) (j i : ℕ), 0 < m →
    (∀ x : ℝ, iteratedDeriv m y x = series f m x) →
    iteratedDeriv (m + 1) y x = expanded f m x

def stepSum (y f : ℝ → ℝ) : Prop :=
  ∀ (m : ℕ) (x : ℝ) (j i : ℕ), 0 < m →
    (∀ x : ℝ, iteratedDeriv m y x = series f m x) →
    iteratedDeriv (m + 1) y x = series f (m + 1) x

def allSum (y f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : ℝ) (j i : ℕ), 0 < n →
    iteratedDeriv n y x = series f n x

end Exercise1230
open Exercise1230

/- Exercise 1230, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = f(x^{2})
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ FuncOfClassK(f, n)

GOAL:
forall (n) (x), n ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, 1)(x^{2})

METHOD:

-/
theorem proof_gap_exercise_1230_1
  (y f : ℝ → ℝ)
  (h3 : ∀ x : ℝ, y x = f (x ^ 2))
  (h4 : ∀ n : ℕ, 0 < n → classK f n)
  : base y f := by
  sorry

/- Exercise 1230, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = f(x^{2})
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ FuncOfClassK(f, n)
5. forall (n) (x), n ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, 1)(x^{2})

GOAL:
forall (n) (x) (j) (i), n ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ j = 0 }^{ floor(n / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (n - i), j!) * (2 * x)^{n - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, n - j)(x^{2}))

METHOD:

-/
theorem proof_gap_exercise_1230_2
  (y f : ℝ → ℝ)
  (h3 : ∀ x : ℝ, y x = f (x ^ 2))
  (h4 : ∀ n : ℕ, 0 < n → classK f n)
  (h5 : base y f)
  : baseSum y f := by
  sorry

/- Exercise 1230, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = f(x^{2})
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ FuncOfClassK(f, n)
5. forall (n) (x), n ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, 1)(x^{2})
6. forall (n) (x) (j) (i), n ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ j = 0 }^{ floor(n / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (n - i), j!) * (2 * x)^{n - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, n - j)(x^{2}))

GOAL:
forall (m) (x) (j) (i), m ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ m ∈ PosIntegerSet ∧ x ∈ RealSet ∧ (forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, m)(x) = sum_{ j = 0 }^{ floor(m / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m - i), j!) * (2 * x)^{m - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - j)(x^{2}))) ⇒ FunDeri(y, 1, m + 1)(x) = (2 * x)^{m + 1} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1)(x^{2}) + frac((m + 1) * m, 1!) * (2 * x)^{m - 1} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m)(x^{2}) + frac((m + 1) * m * (m - 1) * (m - 2), 2!) * (2 * x)^{m - 3} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - 1)(x^{2}) + (sum_{ j = 3 }^{ floor((m + 1) / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m + 1 - i), j!) * (2 * x)^{m + 1 - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1 - j)(x^{2})))

METHOD:
[@method 两边同时对 x 求 导数 @]
-/
theorem proof_gap_exercise_1230_3
  (y f : ℝ → ℝ)
  (h3 : ∀ x : ℝ, y x = f (x ^ 2))
  (h4 : ∀ n : ℕ, 0 < n → classK f n)
  (h5 : base y f)
  (h6 : baseSum y f)
  : stepExpanded y f := by
  sorry

/- Exercise 1230, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = f(x^{2})
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ FuncOfClassK(f, n)
5. forall (n) (x), n ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, 1)(x^{2})
6. forall (n) (x) (j) (i), n ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ j = 0 }^{ floor(n / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (n - i), j!) * (2 * x)^{n - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, n - j)(x^{2}))
7. forall (m) (x) (j) (i), m ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ m ∈ PosIntegerSet ∧ x ∈ RealSet ∧ (forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, m)(x) = sum_{ j = 0 }^{ floor(m / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m - i), j!) * (2 * x)^{m - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - j)(x^{2}))) ⇒ FunDeri(y, 1, m + 1)(x) = (2 * x)^{m + 1} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1)(x^{2}) + frac((m + 1) * m, 1!) * (2 * x)^{m - 1} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m)(x^{2}) + frac((m + 1) * m * (m - 1) * (m - 2), 2!) * (2 * x)^{m - 3} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - 1)(x^{2}) + (sum_{ j = 3 }^{ floor((m + 1) / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m + 1 - i), j!) * (2 * x)^{m + 1 - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1 - j)(x^{2})))

GOAL:
forall (m) (x) (j) (i), m ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ m ∈ PosIntegerSet ∧ x ∈ RealSet ∧ (forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, m)(x) = sum_{ j = 0 }^{ floor(m / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m - i), j!) * (2 * x)^{m - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - j)(x^{2}))) ⇒ FunDeri(y, 1, m + 1)(x) = sum_{ j = 0 }^{ floor((m + 1) / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m + 1 - i), j!) * (2 * x)^{m + 1 - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1 - j)(x^{2}))

METHOD:

-/
theorem proof_gap_exercise_1230_4
  (y f : ℝ → ℝ)
  (h3 : ∀ x : ℝ, y x = f (x ^ 2))
  (h4 : ∀ n : ℕ, 0 < n → classK f n)
  (h5 : base y f)
  (h6 : baseSum y f)
  (h7 : stepExpanded y f)
  : stepSum y f := by
  sorry

/- Exercise 1230, gap 5
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = f(x^{2})
4. forall (n), n ∈ PosIntegerSet ⇒ FuncOfClassK(f, n)
5. forall (n) (x), n ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, 1)(x^{2})
6. forall (n) (x) (j) (i), n ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ j = 0 }^{ floor(n / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (n - i), j!) * (2 * x)^{n - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, n - j)(x^{2}))
7. forall (m) (x) (j) (i), j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ m ∈ PosIntegerSet ∧ x ∈ RealSet ∧ (forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, m)(x) = sum_{ j = 0 }^{ floor(m / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m - i), j!) * (2 * x)^{m - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - j)(x^{2}))) ⇒ FunDeri(y, 1, m + 1)(x) = sum_{ j = 0 }^{ floor((m + 1) / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m + 1 - i), j!) * (2 * x)^{m + 1 - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1 - j)(x^{2}))
GOAL:
forall (n) (x) (j) (i), n ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ j = 0 }^{ floor(n / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (n - i), j!) * (2 * x)^{n - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, n - j)(x^{2}))

METHOD:

-/
theorem proof_gap_exercise_1230_5
  (y f : ℝ → ℝ)
  (h3 : ∀ x : ℝ, y x = f (x ^ 2))
  (h4 : ∀ n : ℕ, 0 < n → classK f n)
  (h5 : base y f)
  (h6 : baseSum y f)
  (h7 : stepSum y f)
  : allSum y f := by
  sorry

/- Exercise 1230, gap 6
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = f(x^{2})
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ FuncOfClassK(f, n)
5. forall (n) (x), n ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, 1)(x^{2})
6. forall (n) (x) (j) (i), n ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ n = 1 ∧ x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ j = 0 }^{ floor(n / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (n - i), j!) * (2 * x)^{n - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, n - j)(x^{2}))
7. forall (m) (x) (j) (i), m ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ m ∈ PosIntegerSet ∧ x ∈ RealSet ∧ (forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, m)(x) = sum_{ j = 0 }^{ floor(m / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m - i), j!) * (2 * x)^{m - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - j)(x^{2}))) ⇒ FunDeri(y, 1, m + 1)(x) = (2 * x)^{m + 1} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1)(x^{2}) + frac((m + 1) * m, 1!) * (2 * x)^{m - 1} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m)(x^{2}) + frac((m + 1) * m * (m - 1) * (m - 2), 2!) * (2 * x)^{m - 3} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - 1)(x^{2}) + (sum_{ j = 3 }^{ floor((m + 1) / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m + 1 - i), j!) * (2 * x)^{m + 1 - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1 - j)(x^{2})))
8. forall (m) (x) (j) (i), m ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ m ∈ PosIntegerSet ∧ x ∈ RealSet ∧ (forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, m)(x) = sum_{ j = 0 }^{ floor(m / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m - i), j!) * (2 * x)^{m - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m - j)(x^{2}))) ⇒ FunDeri(y, 1, m + 1)(x) = sum_{ j = 0 }^{ floor((m + 1) / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (m + 1 - i), j!) * (2 * x)^{m + 1 - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, m + 1 - j)(x^{2}))
9. forall (n) (x) (j) (i), n ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ j = 0 }^{ floor(n / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (n - i), j!) * (2 * x)^{n - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, n - j)(x^{2}))

GOAL:
forall (n) (x) (j) (i), n ∈ NonNegIntegerSet ∧ j ∈ NonNegIntegerSet ∧ i ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ j = 0 }^{ floor(n / 2) } (frac(prod_{ i = 0 }^{ 2 * j - 1 } (n - i), j!) * (2 * x)^{n - 2 * j} * FunDeri(f, fun x [x ∈ RealSet] . x^{2}, n - j)(x^{2}))

METHOD:

-/
theorem proof_gap_exercise_1230_6
  (y f : ℝ → ℝ)
  (h3 : ∀ x : ℝ, y x = f (x ^ 2))
  (h4 : ∀ n : ℕ, 0 < n → classK f n)
  (h5 : base y f)
  (h6 : baseSum y f)
  (h7 : stepExpanded y f)
  (h8 : stepSum y f)
  (h9 : allSum y f)
  : allSum y f := by
  sorry

