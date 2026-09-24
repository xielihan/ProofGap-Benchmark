import Mathlib

set_option autoImplicit false
set_option linter.style.longLine false

-- exercise: exercise_1219_2
-- n is natural with n > 1, equivalently the source integer n > 1.
-- Under this bound, all natural subtractions below agree with integer subtraction.
-- Fractional exponents and all quotients are real-valued.

/- Exercise 1219_2, gap 1
SHA-256: 2d71217bde3caf779fed65e7b0eb8157b1c0a09834f089741b387d7e9d18592c
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 1
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = frac(x, sqrtn(2, 1 - x))
4. n ∈ IntegerSet

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = -sqrtn(2, 1 - x) + frac(1, sqrtn(2, 1 - x))

METHOD:

-/
theorem proof_gap_exercise_1219_2_1
  (f : ℝ → ℝ) (n : ℕ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 1)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = x / Real.sqrt (1 - x))
  (h4 : (n : ℤ) ∈ (Set.univ : Set ℤ))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = -Real.sqrt (1 - x) + 1 / Real.sqrt (1 - x) := by
  sorry

/- Exercise 1219_2, gap 2
SHA-256: 6cbc64b56f3011ef17bb8fbaa90dda46f20372f5adad4471b805ef3ed9225b86
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 1
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = frac(x, sqrtn(2, 1 - x))
4. n ∈ IntegerSet
5. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = -sqrtn(2, 1 - x) + frac(1, sqrtn(2, 1 - x))

GOAL:
forall (x), x ∈ RealSet ∧ x < 1 ⇒ FunDeri(f, 1, n)(x) = frac((2 * n - 3)!!, 2^{n}) * frac(1, (1 - x)^{frac(2 * n - 1, 2)}) + frac((2 * n - 1)!!, 2^{n}) * frac(1, (1 - x)^{frac(2 * n + 1, 2)})

METHOD:

-/
theorem proof_gap_exercise_1219_2_2
  (f : ℝ → ℝ) (n : ℕ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 1)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = x / Real.sqrt (1 - x))
  (h4 : (n : ℤ) ∈ (Set.univ : Set ℤ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = -Real.sqrt (1 - x) + 1 / Real.sqrt (1 - x))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x < 1 →
    iteratedDeriv n f x =
      (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n * (1 / Real.rpow (1 - x) ((2 * (n : ℝ) - 1) / 2)) +
      (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n * (1 / Real.rpow (1 - x) ((2 * (n : ℝ) + 1) / 2)) := by
  sorry

/- Exercise 1219_2, gap 3
SHA-256: e5ead93515ec9fc32d79617c1e53d9ad4ee4f1a351b63350ff6f85e93ff4dabc
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 1
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = frac(x, sqrtn(2, 1 - x))
4. n ∈ IntegerSet
5. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = -sqrtn(2, 1 - x) + frac(1, sqrtn(2, 1 - x))
6. forall (x), x ∈ RealSet ∧ x < 1 ⇒ FunDeri(f, 1, n)(x) = frac((2 * n - 3)!!, 2^{n}) * frac(1, (1 - x)^{frac(2 * n - 1, 2)}) + frac((2 * n - 1)!!, 2^{n}) * frac(1, (1 - x)^{frac(2 * n + 1, 2)})

GOAL:
FunDeri(f, 1, n)(0) = frac((2 * n - 3)!!, 2^{n}) + frac((2 * n - 1)!!, 2^{n})

METHOD:

-/
theorem proof_gap_exercise_1219_2_3
  (f : ℝ → ℝ) (n : ℕ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 1)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = x / Real.sqrt (1 - x))
  (h4 : (n : ℤ) ∈ (Set.univ : Set ℤ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = -Real.sqrt (1 - x) + 1 / Real.sqrt (1 - x))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x < 1 →
    iteratedDeriv n f x =
      (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n * (1 / Real.rpow (1 - x) ((2 * (n : ℝ) - 1) / 2)) +
      (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n * (1 / Real.rpow (1 - x) ((2 * (n : ℝ) + 1) / 2)))
  : iteratedDeriv n f 0 = (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n +
    (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n := by
  sorry

/- Exercise 1219_2, gap 4
SHA-256: f47c2e518581e4f05588c94a86d21932f1cc46c724f5b009cfb29bcb9da717b3
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 1
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = frac(x, sqrtn(2, 1 - x))
4. n ∈ IntegerSet
5. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = -sqrtn(2, 1 - x) + frac(1, sqrtn(2, 1 - x))
6. forall (x), x ∈ RealSet ∧ x < 1 ⇒ FunDeri(f, 1, n)(x) = frac((2 * n - 3)!!, 2^{n}) * frac(1, (1 - x)^{frac(2 * n - 1, 2)}) + frac((2 * n - 1)!!, 2^{n}) * frac(1, (1 - x)^{frac(2 * n + 1, 2)})
7. FunDeri(f, 1, n)(0) = frac((2 * n - 3)!!, 2^{n}) + frac((2 * n - 1)!!, 2^{n})

GOAL:
frac((2 * n - 3)!!, 2^{n}) + frac((2 * n - 1)!!, 2^{n}) = frac(n * (2 * n - 3)!!, 2^{n - 1})

METHOD:

-/
theorem proof_gap_exercise_1219_2_4
  (f : ℝ → ℝ) (n : ℕ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 1)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = x / Real.sqrt (1 - x))
  (h4 : (n : ℤ) ∈ (Set.univ : Set ℤ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = -Real.sqrt (1 - x) + 1 / Real.sqrt (1 - x))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x < 1 →
    iteratedDeriv n f x =
      (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n * (1 / Real.rpow (1 - x) ((2 * (n : ℝ) - 1) / 2)) +
      (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n * (1 / Real.rpow (1 - x) ((2 * (n : ℝ) + 1) / 2)))
  (h7 : iteratedDeriv n f 0 = (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n +
    (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n)
  : (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n +
    (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n = (n : ℝ) * (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ (n - 1) := by
  sorry

/- Exercise 1219_2, gap 5
SHA-256: a97c3077b152b9d5e7ac0cdafb047c39a26b0c502a6bec7debc233bd5dc84599
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. n ∈ NonNegIntegerSet ∧ n > 1
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = frac(x, sqrtn(2, 1 - x))
4. n ∈ IntegerSet
5. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-∞, 1) ⇒ f(x) = -sqrtn(2, 1 - x) + frac(1, sqrtn(2, 1 - x))
6. forall (x), x ∈ RealSet ∧ x < 1 ⇒ FunDeri(f, 1, n)(x) = frac((2 * n - 3)!!, 2^{n}) * frac(1, (1 - x)^{frac(2 * n - 1, 2)}) + frac((2 * n - 1)!!, 2^{n}) * frac(1, (1 - x)^{frac(2 * n + 1, 2)})
7. FunDeri(f, 1, n)(0) = frac((2 * n - 3)!!, 2^{n}) + frac((2 * n - 1)!!, 2^{n})
8. frac((2 * n - 3)!!, 2^{n}) + frac((2 * n - 1)!!, 2^{n}) = frac(n * (2 * n - 3)!!, 2^{n - 1})

GOAL:
FunDeri(f, 1, n)(0) = frac(n * (2 * n - 3)!!, 2^{n - 1})

METHOD:

-/
theorem proof_gap_exercise_1219_2_5
  (f : ℝ → ℝ) (n : ℕ)
  (h2 : n ∈ (Set.univ : Set ℕ) ∧ n > 1)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = x / Real.sqrt (1 - x))
  (h4 : (n : ℤ) ∈ (Set.univ : Set ℤ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Iio (1 : ℝ) →
    f x = -Real.sqrt (1 - x) + 1 / Real.sqrt (1 - x))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x < 1 →
    iteratedDeriv n f x =
      (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n * (1 / Real.rpow (1 - x) ((2 * (n : ℝ) - 1) / 2)) +
      (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n * (1 / Real.rpow (1 - x) ((2 * (n : ℝ) + 1) / 2)))
  (h7 : iteratedDeriv n f 0 = (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n +
    (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n)
  (h8 : (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ n +
    (Nat.doubleFactorial (2 * n - 1) : ℝ) / (2 : ℝ) ^ n = (n : ℝ) * (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ (n - 1))
  : iteratedDeriv n f 0 = (n : ℝ) * (Nat.doubleFactorial (2 * n - 3) : ℝ) / (2 : ℝ) ^ (n - 1) := by
  sorry
