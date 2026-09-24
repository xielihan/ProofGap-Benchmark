import Mathlib

/- SmoothFunc follows the theorem library, Thm 287.
Gap 9 retains the source claim of differentiability of every iterated derivative,
which is false in general; see the semantic review. -/

/- Exercise 1013, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. DiffableFuncAt(y, c)
GOAL:
a + b * c^{2} = frac(m^{2}, c)

METHOD:

-/
theorem proof_gap_exercise_1013_1
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : DifferentiableAt ℝ y c)
  : a + b * c ^ 2 = m ^ 2 / c := by
  sorry

/- Exercise 1013, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. a + b * c^{2} = frac(m^{2}, c)
8. DiffableFuncAt(y, c)
GOAL:
FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(c)

METHOD:

-/
theorem proof_gap_exercise_1013_2
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : a + b * c ^ 2 = m ^ 2 / c)
  (h8 : DifferentiableAt ℝ y c)
  : deriv (fun x : ℝ => a + b * x ^ 2) (c) = deriv (fun x : ℝ => m ^ 2 / |x|) (c) := by
  sorry

/- Exercise 1013, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. a + b * c^{2} = frac(m^{2}, c)
8. FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(c)

GOAL:
2 * b * c = -frac(m^{2}, c^{2})

METHOD:

-/
theorem proof_gap_exercise_1013_3
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : a + b * c ^ 2 = m ^ 2 / c)
  (h8 : deriv (fun x : ℝ => a + b * x ^ 2) (c) = deriv (fun x : ℝ => m ^ 2 / |x|) (c))
  : 2 * b * c = -(m ^ 2 / c ^ 2) := by
  sorry

/- Exercise 1013, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. a + b * c^{2} = frac(m^{2}, c)
8. FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(c)
9. 2 * b * c = -frac(m^{2}, c^{2})

GOAL:
a + b * c^{2} = frac(m^{2}, c)

METHOD:

-/
theorem proof_gap_exercise_1013_4
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : a + b * c ^ 2 = m ^ 2 / c)
  (h8 : deriv (fun x : ℝ => a + b * x ^ 2) (c) = deriv (fun x : ℝ => m ^ 2 / |x|) (c))
  (h9 : 2 * b * c = -(m ^ 2 / c ^ 2))
  : a + b * c ^ 2 = m ^ 2 / c := by
  sorry

/- Exercise 1013, gap 5
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. a + b * c^{2} = frac(m^{2}, c)
8. FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(c)
9. 2 * b * c = -frac(m^{2}, c^{2})
10. a + b * c^{2} = frac(m^{2}, c)

GOAL:
2 * b * c = -frac(m^{2}, c^{2})

METHOD:

-/
theorem proof_gap_exercise_1013_5
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : a + b * c ^ 2 = m ^ 2 / c)
  (h8 : deriv (fun x : ℝ => a + b * x ^ 2) (c) = deriv (fun x : ℝ => m ^ 2 / |x|) (c))
  (h9 : 2 * b * c = -(m ^ 2 / c ^ 2))
  (h10 : a + b * c ^ 2 = m ^ 2 / c)
  : 2 * b * c = -(m ^ 2 / c ^ 2) := by
  sorry

/- Exercise 1013, gap 6
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. a + b * c^{2} = frac(m^{2}, c)
8. FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(c)
9. 2 * b * c = -frac(m^{2}, c^{2})
10. a + b * c^{2} = frac(m^{2}, c)
11. 2 * b * c = -frac(m^{2}, c^{2})

GOAL:
a = frac(3 * m^{2}, 2 * c)

METHOD:

-/
theorem proof_gap_exercise_1013_6
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : a + b * c ^ 2 = m ^ 2 / c)
  (h8 : deriv (fun x : ℝ => a + b * x ^ 2) (c) = deriv (fun x : ℝ => m ^ 2 / |x|) (c))
  (h9 : 2 * b * c = -(m ^ 2 / c ^ 2))
  (h10 : a + b * c ^ 2 = m ^ 2 / c)
  (h11 : 2 * b * c = -(m ^ 2 / c ^ 2))
  : a = 3 * m ^ 2 / (2 * c) := by
  sorry

/- Exercise 1013, gap 7
PROOF GAP @7
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. a + b * c^{2} = frac(m^{2}, c)
8. FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(c)
9. 2 * b * c = -frac(m^{2}, c^{2})
10. a + b * c^{2} = frac(m^{2}, c)
11. 2 * b * c = -frac(m^{2}, c^{2})
12. a = frac(3 * m^{2}, 2 * c)

GOAL:
b = -frac(m^{2}, 2 * c^{3})

METHOD:

-/
theorem proof_gap_exercise_1013_7
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : a + b * c ^ 2 = m ^ 2 / c)
  (h8 : deriv (fun x : ℝ => a + b * x ^ 2) (c) = deriv (fun x : ℝ => m ^ 2 / |x|) (c))
  (h9 : 2 * b * c = -(m ^ 2 / c ^ 2))
  (h10 : a + b * c ^ 2 = m ^ 2 / c)
  (h11 : 2 * b * c = -(m ^ 2 / c ^ 2))
  (h12 : a = 3 * m ^ 2 / (2 * c))
  : b = -(m ^ 2 / (2 * c ^ 3)) := by
  sorry

/- Exercise 1013, gap 8
PROOF GAP @8
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. a + b * c^{2} = frac(m^{2}, c)
8. FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(c)
9. 2 * b * c = -frac(m^{2}, c^{2})
10. a + b * c^{2} = frac(m^{2}, c)
11. 2 * b * c = -frac(m^{2}, c^{2})
12. a = frac(3 * m^{2}, 2 * c)
13. b = -frac(m^{2}, 2 * c^{3})

GOAL:
FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(-c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(-c)

METHOD:

-/
theorem proof_gap_exercise_1013_8
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : a + b * c ^ 2 = m ^ 2 / c)
  (h8 : deriv (fun x : ℝ => a + b * x ^ 2) (c) = deriv (fun x : ℝ => m ^ 2 / |x|) (c))
  (h9 : 2 * b * c = -(m ^ 2 / c ^ 2))
  (h10 : a + b * c ^ 2 = m ^ 2 / c)
  (h11 : 2 * b * c = -(m ^ 2 / c ^ 2))
  (h12 : a = 3 * m ^ 2 / (2 * c))
  (h13 : b = -(m ^ 2 / (2 * c ^ 3)))
  : deriv (fun x : ℝ => a + b * x ^ 2) (-c) = deriv (fun x : ℝ => m ^ 2 / |x|) (-c) := by
  sorry

/- Exercise 1013, gap 9
PROOF GAP @9
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. c ∈ RealSet ∧ c > 0
5. m ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ y(x) = cases{ a + b * x^{2} if |x| ≤ c; frac(m^{2}, |x|) if |x| > c }
7. a + b * c^{2} = frac(m^{2}, c)
8. FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(c)
9. 2 * b * c = -frac(m^{2}, c^{2})
10. a + b * c^{2} = frac(m^{2}, c)
11. 2 * b * c = -frac(m^{2}, c^{2})
12. a = frac(3 * m^{2}, 2 * c)
13. b = -frac(m^{2}, 2 * c^{3})
14. FunDeri(fun x [x ∈ RealSet] . a + b * x^{2}, 1, 1)(-c) = FunDeri(fun x [x ∈ RealSet] . frac(m^{2}, |x|), 1, 1)(-c)

GOAL:
(a, b) = (frac(3 * m^{2}, 2 * c), -frac(m^{2}, 2 * c^{3})) ⇒ SmoothFunc(y)

METHOD:

-/
theorem proof_gap_exercise_1013_9
  (y : ℝ → ℝ) (a b c m : ℝ)
  (h4 : c > 0)
  (h6 : ∀ x : ℝ, y x = if |x| ≤ c then a + b * x ^ 2 else m ^ 2 / |x|)
  (h7 : a + b * c ^ 2 = m ^ 2 / c)
  (h8 : deriv (fun x : ℝ => a + b * x ^ 2) (c) = deriv (fun x : ℝ => m ^ 2 / |x|) (c))
  (h9 : 2 * b * c = -(m ^ 2 / c ^ 2))
  (h10 : a + b * c ^ 2 = m ^ 2 / c)
  (h11 : 2 * b * c = -(m ^ 2 / c ^ 2))
  (h12 : a = 3 * m ^ 2 / (2 * c))
  (h13 : b = -(m ^ 2 / (2 * c ^ 3)))
  (h14 : deriv (fun x : ℝ => a + b * x ^ 2) (-c) = deriv (fun x : ℝ => m ^ 2 / |x|) (-c))
  : (a, b) = (3 * m ^ 2 / (2 * c), -(m ^ 2 / (2 * c ^ 3))) → (∀ k : ℕ, Differentiable ℝ (iteratedDeriv k y)) := by
  sorry

