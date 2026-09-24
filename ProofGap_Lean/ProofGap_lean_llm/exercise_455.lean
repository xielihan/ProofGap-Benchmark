import Mathlib

open scoped BigOperators Topology
open Filter

namespace Exercise455

-- On x > 0 and nonzero integer d, this is the positive d-th root,
-- including reciprocal roots for negative d.
noncomputable def root (d : ℤ) (x : ℝ) : ℝ := Real.rpow x (1 / (d : ℝ))

noncomputable def quotient (m n : ℤ) (x : ℝ) : ℝ :=
  (root m x - 1) / (root n x - 1)

-- Integer endpoints preserve subtraction and the inclusive 0,...,d-1 range.
noncomputable def powerSum (d : ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (0 : ℤ) (d - 1), Real.rpow x ((k : ℝ) / (d : ℝ))

-- Punctured approach within the original positive-real domain.
def HasLimit (m n : ℤ) (L : ℝ) : Prop :=
  Tendsto (quotient m n) (𝓝[({x : ℝ | 0 < x ∧ x ≠ 1})] (1 : ℝ)) (𝓝 L)

end Exercise455

open Exercise455

/- Exercise 455, gap 1
PROOF GAP @1
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0

GOAL:
forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))

METHOD:

-/
theorem proof_gap_exercise_455_1
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x := by
  sorry

/- Exercise 455, gap 2
PROOF GAP @2
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ x ≠ 1 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
GOAL:
m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)

METHOD:

-/
theorem proof_gap_exercise_455_2
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ x ≠ 1 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  : 0 < m → 0 < n → HasLimit m n ((n : ℝ) / (m : ℝ)) := by
  sorry

/- Exercise 455, gap 3
PROOF GAP @3
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
6. m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)

GOAL:
forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `m'` ∈ PosIntegerSet)

METHOD:

-/
theorem proof_gap_exercise_455_3
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  (h6 : 0 < m → 0 < n → HasLimit m n ((n : ℝ) / (m : ℝ)))
  : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < m' := by
  sorry

/- Exercise 455, gap 4
PROOF GAP @4
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ x ≠ 1 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
6. m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)
7. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `m'` ∈ PosIntegerSet)
GOAL:
forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `n'` ∈ PosIntegerSet)

METHOD:

-/
theorem proof_gap_exercise_455_4
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ x ≠ 1 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  (h6 : 0 < m → 0 < n → HasLimit m n ((n : ℝ) / (m : ℝ)))
  (h7 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < m')
  : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < n' := by
  sorry

/- Exercise 455, gap 5
PROOF GAP @5
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ x ≠ 1 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
6. m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)
7. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `m'` ∈ PosIntegerSet)
8. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `n'` ∈ PosIntegerSet)
GOAL:
forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ⇒ (forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(1 - sqrtn(`m'`, x), 1 - sqrtn(`n'`, x)) * frac(sqrtn(`n'`, x), sqrtn(`m'`, x))))

METHOD:

-/
theorem proof_gap_exercise_455_5
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ x ≠ 1 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  (h6 : 0 < m → 0 < n → HasLimit m n ((n : ℝ) / (m : ℝ)))
  (h7 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < m')
  (h8 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < n')
  : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → quotient m n x = (1 - root m' x) / (1 - root n' x) * (root n' x / root m' x) := by
  sorry

/- Exercise 455, gap 6
PROOF GAP @6
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ x ≠ 1 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
6. m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)
7. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `m'` ∈ PosIntegerSet)
8. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `n'` ∈ PosIntegerSet)
9. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ⇒ (forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(1 - sqrtn(`m'`, x), 1 - sqrtn(`n'`, x)) * frac(sqrtn(`n'`, x), sqrtn(`m'`, x))))
GOAL:
forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(`n'`, `m'`))

METHOD:

-/
theorem proof_gap_exercise_455_6
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ x ≠ 1 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  (h6 : 0 < m → 0 < n → HasLimit m n ((n : ℝ) / (m : ℝ)))
  (h7 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < m')
  (h8 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < n')
  (h9 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → quotient m n x = (1 - root m' x) / (1 - root n' x) * (root n' x / root m' x))
  : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → HasLimit m n ((n' : ℝ) / (m' : ℝ)) := by
  sorry

/- Exercise 455, gap 7
PROOF GAP @7
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
6. m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)
7. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `m'` ∈ PosIntegerSet)
8. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `n'` ∈ PosIntegerSet)
9. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ⇒ (forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(1 - sqrtn(`m'`, x), 1 - sqrtn(`n'`, x)) * frac(sqrtn(`n'`, x), sqrtn(`m'`, x))))
10. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(`n'`, `m'`))

GOAL:
forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(`n'`, `m'`) = frac(n, m))

METHOD:

-/
theorem proof_gap_exercise_455_7
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  (h6 : 0 < m → 0 < n → HasLimit m n ((n : ℝ) / (m : ℝ)))
  (h7 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < m')
  (h8 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < n')
  (h9 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → quotient m n x = (1 - root m' x) / (1 - root n' x) * (root n' x / root m' x))
  (h10 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → HasLimit m n ((n' : ℝ) / (m' : ℝ)))
  : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → (n' : ℝ) / (m' : ℝ) = (n : ℝ) / (m : ℝ) := by
  sorry

/- Exercise 455, gap 8
PROOF GAP @8
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
6. m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)
7. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `m'` ∈ PosIntegerSet)
8. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `n'` ∈ PosIntegerSet)
9. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ⇒ (forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(1 - sqrtn(`m'`, x), 1 - sqrtn(`n'`, x)) * frac(sqrtn(`n'`, x), sqrtn(`m'`, x))))
10. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(`n'`, `m'`))
11. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(`n'`, `m'`) = frac(n, m))

GOAL:
forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m))

METHOD:

-/
theorem proof_gap_exercise_455_8
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  (h6 : 0 < m → 0 < n → HasLimit m n ((n : ℝ) / (m : ℝ)))
  (h7 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < m')
  (h8 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < n')
  (h9 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → quotient m n x = (1 - root m' x) / (1 - root n' x) * (root n' x / root m' x))
  (h10 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → HasLimit m n ((n' : ℝ) / (m' : ℝ)))
  (h11 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → (n' : ℝ) / (m' : ℝ) = (n : ℝ) / (m : ℝ))
  : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → HasLimit m n ((n : ℝ) / (m : ℝ)) := by
  sorry

/- Exercise 455, gap 9
PROOF GAP @9
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ x ≠ 1 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
6. m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)
7. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `m'` ∈ PosIntegerSet)
8. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `n'` ∈ PosIntegerSet)
9. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ⇒ (forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(1 - sqrtn(`m'`, x), 1 - sqrtn(`n'`, x)) * frac(sqrtn(`n'`, x), sqrtn(`m'`, x))))
10. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(`n'`, `m'`))
11. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(`n'`, `m'`) = frac(n, m))
12. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m))
GOAL:
m ∈ PosIntegerSet ∧ n ∈ NegIntegerSet ∨ m ∈ NegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)

METHOD:

-/
theorem proof_gap_exercise_455_9
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ x ≠ 1 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  (h6 : 0 < m → 0 < n → HasLimit m n ((n : ℝ) / (m : ℝ)))
  (h7 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < m')
  (h8 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < n')
  (h9 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → quotient m n x = (1 - root m' x) / (1 - root n' x) * (root n' x / root m' x))
  (h10 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → HasLimit m n ((n' : ℝ) / (m' : ℝ)))
  (h11 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → (n' : ℝ) / (m' : ℝ) = (n : ℝ) / (m : ℝ))
  (h12 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → HasLimit m n ((n : ℝ) / (m : ℝ)))
  : (0 < m ∧ n < 0) ∨ (m < 0 ∧ 0 < n) → HasLimit m n ((n : ℝ) / (m : ℝ)) := by
  sorry

/- Exercise 455, gap 10
PROOF GAP @10
ASSUM:
1. m ∈ IntegerSet
2. n ∈ IntegerSet
3. m ≠ 0
4. n ≠ 0
5. forall (x), x ∈ RealSet ∧ x > 0 ∧ x ≠ 1 ∧ m ∈ PosIntegerSet ∧ n ∈ PosIntegerSet ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(sum_{ k = 0 }^{ n - 1 } (x^{frac(k, n)}), sum_{ k = 0 }^{ m - 1 } (x^{frac(k, m)}))
6. m ∈ PosIntegerSet ⇒ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n * 1, m * 1)
7. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `m'` ∈ PosIntegerSet)
8. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ `n'` ∈ PosIntegerSet)
9. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ⇒ (forall (x), x ∈ RealSet ∧ x > 0 ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1) = frac(1 - sqrtn(`m'`, x), 1 - sqrtn(`n'`, x)) * frac(sqrtn(`n'`, x), sqrtn(`m'`, x))))
10. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(`n'`, `m'`))
11. forall (`m'`), `m'` ∈ IntegerSet ⇒ (forall (`n'`), `n'` ∈ IntegerSet ∧ m ∈ NegIntegerSet ∧ n ∈ NegIntegerSet ∧ `m'` = -m ∧ `n'` = -n ⇒ frac(`n'`, `m'`) = frac(n, m))
12. m ∈ PosIntegerSet ∧ n ∈ NegIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = -frac(-n, m)
13. m ∈ NegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = -frac(n, -m)
GOAL:
lim_{ x → 1 } (frac(sqrtn(m, x) - 1, sqrtn(n, x) - 1)) = frac(n, m)

METHOD:

-/
theorem proof_gap_exercise_455_10
  (m n : ℤ)
  (h1 : m ∈ (Set.univ : Set ℤ))
  (h2 : n ∈ (Set.univ : Set ℤ))
  (h3 : m ≠ 0)
  (h4 : n ≠ 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ x ≠ 1 ∧ 0 < m ∧ 0 < n → quotient m n x = powerSum n x / powerSum m x)
  (h6 : 0 < m → 0 < n → HasLimit m n (((n : ℝ) * 1) / ((m : ℝ) * 1)))
  (h7 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < m')
  (h8 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → 0 < n')
  (h9 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → quotient m n x = (1 - root m' x) / (1 - root n' x) * (root n' x / root m' x))
  (h10 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → HasLimit m n ((n' : ℝ) / (m' : ℝ)))
  (h11 : ∀ m' : ℤ, m' ∈ (Set.univ : Set ℤ) → ∀ n' : ℤ, n' ∈ (Set.univ : Set ℤ) ∧ m < 0 ∧ n < 0 ∧ m' = -m ∧ n' = -n → (n' : ℝ) / (m' : ℝ) = (n : ℝ) / (m : ℝ))
  (h12 : 0 < m ∧ n < 0 → HasLimit m n (- (-(n : ℝ) / (m : ℝ))))
  (h13 : m < 0 ∧ 0 < n → HasLimit m n (- ((n : ℝ) / -(m : ℝ))))
  : HasLimit m n ((n : ℝ) / (m : ℝ)) := by
  sorry

