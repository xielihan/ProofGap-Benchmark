import Mathlib

/- Real rational powers with odd denominator are interpreted using the real
cube root, as required by the astroid on all four quadrants.
FunDeri(y, 1, n) is evaluated at the ambient x, following the original y'(x).
Source defects are retained; see reviews/exercise_1599.json. -/
noncomputable def exercise1599CubeRoot (t : ℝ) : ℝ :=
  if t < 0 then -Real.rpow (-t) (1 / 3 : ℝ) else Real.rpow t (1 / 3 : ℝ)

/- Exercise 1599, gap 1
PROOF GAP @1
ASSUM:
1. x ∈ RealSet
2. y : RealSet → RealSet
3. a ∈ RealSet
4. R ∈ RealSet
5. a > 0
6. y(x) ∈ RealSet
7. x^{frac(2, 3)} + y(x)^{frac(2, 3)} = a^{frac(2, 3)}

GOAL:
x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 1) = -sqrtn(3, frac(y(x), x))

METHOD:

-/
theorem proof_gap_exercise_1599_1
  (x : ℝ) (y : ℝ → ℝ) (a R : ℝ)
  (h5 : a > 0)
  (h7 : exercise1599CubeRoot x ^ 2 + exercise1599CubeRoot (y x) ^ 2 = exercise1599CubeRoot a ^ 2)
  : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 1 y x = -exercise1599CubeRoot (y x / x) := by
  sorry

/- Exercise 1599, gap 2
PROOF GAP @2
ASSUM:
1. x ∈ RealSet
2. y : RealSet → RealSet
3. a ∈ RealSet
4. R ∈ RealSet
5. a > 0
6. y(x) ∈ RealSet
7. x^{frac(2, 3)} + y(x)^{frac(2, 3)} = a^{frac(2, 3)}
8. x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 1) = -sqrtn(3, frac(y(x), x))

GOAL:
x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 2) = frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)})

METHOD:

-/
theorem proof_gap_exercise_1599_2
  (x : ℝ) (y : ℝ → ℝ) (a R : ℝ)
  (h5 : a > 0)
  (h7 : exercise1599CubeRoot x ^ 2 + exercise1599CubeRoot (y x) ^ 2 = exercise1599CubeRoot a ^ 2)
  (h8 : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 1 y x = -exercise1599CubeRoot (y x / x))
  : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 2 y x = exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x)) := by
  sorry

/- Exercise 1599, gap 3
PROOF GAP @3
ASSUM:
1. x ∈ RealSet
2. y : RealSet → RealSet
3. a ∈ RealSet
4. R ∈ RealSet
5. a > 0
6. y(x) ∈ RealSet
7. x^{frac(2, 3)} + y(x)^{frac(2, 3)} = a^{frac(2, 3)}
8. x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 1) = -sqrtn(3, frac(y(x), x))
9. x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 2) = frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)})

GOAL:
R = frac((1 + frac(y(x), x)^{frac(2, 3)})^{frac(3, 2)}, |frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)})|)

METHOD:

-/
theorem proof_gap_exercise_1599_3
  (x : ℝ) (y : ℝ → ℝ) (a R : ℝ)
  (h5 : a > 0)
  (h7 : exercise1599CubeRoot x ^ 2 + exercise1599CubeRoot (y x) ^ 2 = exercise1599CubeRoot a ^ 2)
  (h8 : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 1 y x = -exercise1599CubeRoot (y x / x))
  (h9 : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 2 y x = exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x)))
  : R = Real.rpow (1 + exercise1599CubeRoot (y x / x) ^ 2) (3 / 2 : ℝ) / |exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x))| := by
  sorry

/- Exercise 1599, gap 4
PROOF GAP @4
ASSUM:
1. x ∈ RealSet
2. y : RealSet → RealSet
3. a ∈ RealSet
4. R ∈ RealSet
5. a > 0
6. y(x) ∈ RealSet
7. x^{frac(2, 3)} + y(x)^{frac(2, 3)} = a^{frac(2, 3)}
8. x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 1) = -sqrtn(3, frac(y(x), x))
9. x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 2) = frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)})
10. R = frac((1 + frac(y(x), x)^{frac(2, 3)})^{frac(3, 2)}, |frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)})|)

GOAL:
R = |frac(frac(a, x), frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)}))|

METHOD:

-/
theorem proof_gap_exercise_1599_4
  (x : ℝ) (y : ℝ → ℝ) (a R : ℝ)
  (h5 : a > 0)
  (h7 : exercise1599CubeRoot x ^ 2 + exercise1599CubeRoot (y x) ^ 2 = exercise1599CubeRoot a ^ 2)
  (h8 : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 1 y x = -exercise1599CubeRoot (y x / x))
  (h9 : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 2 y x = exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x)))
  (h10 : R = Real.rpow (1 + exercise1599CubeRoot (y x / x) ^ 2) (3 / 2 : ℝ) / |exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x))|)
  : R = |(a / x) / (exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x)))| := by
  sorry

/- Exercise 1599, gap 5
PROOF GAP @5
ASSUM:
1. x ∈ RealSet
2. y : RealSet → RealSet
3. a ∈ RealSet
4. R ∈ RealSet
5. a > 0
6. y(x) ∈ RealSet
7. x^{frac(2, 3)} + y(x)^{frac(2, 3)} = a^{frac(2, 3)}
8. x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 1) = -sqrtn(3, frac(y(x), x))
9. x ≠ 0 ∧ y(x) ≠ 0 ⇒ FunDeri(y, 1, 2) = frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)})
10. R = frac((1 + frac(y(x), x)^{frac(2, 3)})^{frac(3, 2)}, |frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)})|)
11. R = |frac(frac(a, x), frac(a^{frac(2, 3)}, 3 * x^{frac(4, 3)} * y(x)^{frac(1, 3)}))|

GOAL:
R = 3 * |a * x * y(x)|^{frac(1, 3)}

METHOD:

-/
theorem proof_gap_exercise_1599_5
  (x : ℝ) (y : ℝ → ℝ) (a R : ℝ)
  (h5 : a > 0)
  (h7 : exercise1599CubeRoot x ^ 2 + exercise1599CubeRoot (y x) ^ 2 = exercise1599CubeRoot a ^ 2)
  (h8 : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 1 y x = -exercise1599CubeRoot (y x / x))
  (h9 : x ≠ 0 ∧ y x ≠ 0 → iteratedDeriv 2 y x = exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x)))
  (h10 : R = Real.rpow (1 + exercise1599CubeRoot (y x / x) ^ 2) (3 / 2 : ℝ) / |exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x))|)
  (h11 : R = |(a / x) / (exercise1599CubeRoot a ^ 2 / (3 * exercise1599CubeRoot x ^ 4 * exercise1599CubeRoot (y x)))|)
  : R = 3 * exercise1599CubeRoot |a * x * y x| := by
  sorry

