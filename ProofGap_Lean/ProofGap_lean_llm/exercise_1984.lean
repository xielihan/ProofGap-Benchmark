import Mathlib

set_option linter.style.longLine false

namespace Exercise1984

-- The differential on (0,1), represented by its coefficient in the coordinate dt.
-- The subtype retains the lambda's domain; no claim that the outer z lies in it.
noncomputable def restrictedDiff (f : ℝ → ℝ) : Set.Ioo (0 : ℝ) 1 → ℝ :=
  fun t => derivWithin f (Set.Ioo 0 1) t.val

-- Derivative equalities mean the ordinary derivative exists with the stated value.
-- All functions are global real functions, with conditions only on the stated interval.
def originalPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ -1 < t ∧ t < 1 →
    HasDerivAt F (t ^ 5 / Real.sqrt (1 - t ^ 2) * deriv (fun u : ℝ => u) t) t}

def negativePrimitives : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 < t ∧ t < 1 →
    HasDerivAt G ((1 - t ^ 2) ^ 2 * deriv (fun u : ℝ => u) t) t ∧ F t = -G t}

def polynomialFamily : Set (ℝ → ℝ) :=
  {F | ∃ c : ℝ, c ∈ (Set.univ : Set ℝ) ∧
    ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 < t ∧ t < 1 →
      F t = -t + (2 / 3 : ℝ) * t ^ 3 - (1 / 5 : ℝ) * t ^ 5 + c}

def answerFamily : Set (ℝ → ℝ) :=
  {F | ∃ c : ℝ, c ∈ (Set.univ : Set ℝ) ∧
    ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ -1 < t ∧ t < 1 →
      F t = -Real.sqrt (1 - t ^ 2) + (2 / 3 : ℝ) * Real.sqrt (1 - t ^ 2) ^ 3
        - (1 / 5 : ℝ) * Real.sqrt (1 - t ^ 2) ^ 5 + c}

/- Exercise 1984, gap 1
PROOF GAP @1
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet

GOAL:
frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}

METHOD:

-/
theorem proof_gap_exercise_1984_1
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)) := by
  sorry

/- Exercise 1984, gap 2
PROOF GAP @2
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}

GOAL:
sqrtn(2, 1 - x^{2}) = z

METHOD:

-/
theorem proof_gap_exercise_1984_2
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  : Real.sqrt (1 - x ^ 2) = z := by
  sorry

/- Exercise 1984, gap 3
PROOF GAP @3
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}
5. sqrtn(2, 1 - x^{2}) = z

GOAL:
0 < x ⇒ x < 1 ⇒ 0 < z

METHOD:

-/
theorem proof_gap_exercise_1984_3
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  (h5 : Real.sqrt (1 - x ^ 2) = z)
  : 0 < x → x < 1 → 0 < z := by
  sorry

/- Exercise 1984, gap 4
PROOF GAP @4
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}
5. sqrtn(2, 1 - x^{2}) = z
6. 0 < x ⇒ x < 1 ⇒ 0 < z

GOAL:
0 < x ⇒ x < 1 ⇒ z < 1

METHOD:

-/
theorem proof_gap_exercise_1984_4
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  (h5 : Real.sqrt (1 - x ^ 2) = z)
  (h6 : 0 < x → x < 1 → 0 < z)
  : 0 < x → x < 1 → z < 1 := by
  sorry

/- Exercise 1984, gap 5
PROOF GAP @5
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}
5. sqrtn(2, 1 - x^{2}) = z
6. 0 < x ⇒ x < 1 ⇒ 0 < z
7. 0 < x ⇒ x < 1 ⇒ z < 1

GOAL:
0 < x ⇒ x < 1 ⇒ x = sqrtn(2, 1 - z^{2})

METHOD:

-/
theorem proof_gap_exercise_1984_5
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  (h5 : Real.sqrt (1 - x ^ 2) = z)
  (h6 : 0 < x → x < 1 → 0 < z)
  (h7 : 0 < x → x < 1 → z < 1)
  : 0 < x → x < 1 → x = Real.sqrt (1 - z ^ 2) := by
  sorry

/- Exercise 1984, gap 6
PROOF GAP @6
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}
5. sqrtn(2, 1 - x^{2}) = z
6. 0 < x ⇒ x < 1 ⇒ 0 < z
7. 0 < x ⇒ x < 1 ⇒ z < 1
8. 0 < x ⇒ x < 1 ⇒ x = sqrtn(2, 1 - z^{2})

GOAL:
0 < x ⇒ x < 1 ⇒ diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . x) = -frac(z, sqrtn(2, 1 - z^{2})) * diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . z)

METHOD:

-/
theorem proof_gap_exercise_1984_6
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  (h5 : Real.sqrt (1 - x ^ 2) = z)
  (h6 : 0 < x → x < 1 → 0 < z)
  (h7 : 0 < x → x < 1 → z < 1)
  (h8 : 0 < x → x < 1 → x = Real.sqrt (1 - z ^ 2))
  : 0 < x → x < 1 → restrictedDiff (fun _ : ℝ => x) =
    (fun t => -(z / Real.sqrt (1 - z ^ 2)) * restrictedDiff (fun u : ℝ => u) t) := by
  sorry

/- Exercise 1984, gap 7
PROOF GAP @7
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}
5. sqrtn(2, 1 - x^{2}) = z
6. 0 < x ⇒ x < 1 ⇒ 0 < z
7. 0 < x ⇒ x < 1 ⇒ z < 1
8. 0 < x ⇒ x < 1 ⇒ x = sqrtn(2, 1 - z^{2})
9. 0 < x ⇒ x < 1 ⇒ diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . x) = -frac(z, sqrtn(2, 1 - z^{2})) * diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . z)

GOAL:
0 < x ⇒ x < 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ∧ -1 < x ∧ x < 1 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(x^{5}, sqrtn(2, 1 - x^{2})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = (1 - z^{2})^{2} * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_4`(z) = -`F_3`(z)) }

METHOD:

-/
theorem proof_gap_exercise_1984_7
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  (h5 : Real.sqrt (1 - x ^ 2) = z)
  (h6 : 0 < x → x < 1 → 0 < z)
  (h7 : 0 < x → x < 1 → z < 1)
  (h8 : 0 < x → x < 1 → x = Real.sqrt (1 - z ^ 2))
  (h9 : 0 < x → x < 1 → restrictedDiff (fun _ : ℝ => x) =
    (fun t => -(z / Real.sqrt (1 - z ^ 2)) * restrictedDiff (fun u : ℝ => u) t))
  : 0 < x → x < 1 → originalPrimitives = negativePrimitives := by
  sorry

/- Exercise 1984, gap 8
PROOF GAP @8
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}
5. sqrtn(2, 1 - x^{2}) = z
6. 0 < x ⇒ x < 1 ⇒ 0 < z
7. 0 < x ⇒ x < 1 ⇒ z < 1
8. 0 < x ⇒ x < 1 ⇒ x = sqrtn(2, 1 - z^{2})
9. 0 < x ⇒ x < 1 ⇒ diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . x) = -frac(z, sqrtn(2, 1 - z^{2})) * diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . z)
10. 0 < x ⇒ x < 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ∧ -1 < x ∧ x < 1 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(x^{5}, sqrtn(2, 1 - x^{2})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = (1 - z^{2})^{2} * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_4`(z) = -`F_3`(z)) }

GOAL:
{ `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = (1 - z^{2})^{2} * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_6`(z) = -`F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ `F_7`(z) = -z + frac(2, 3) * z^{3} - frac(1, 5) * z^{5} + C) }

METHOD:

-/
theorem proof_gap_exercise_1984_8
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  (h5 : Real.sqrt (1 - x ^ 2) = z)
  (h6 : 0 < x → x < 1 → 0 < z)
  (h7 : 0 < x → x < 1 → z < 1)
  (h8 : 0 < x → x < 1 → x = Real.sqrt (1 - z ^ 2))
  (h9 : 0 < x → x < 1 → restrictedDiff (fun _ : ℝ => x) =
    (fun t => -(z / Real.sqrt (1 - z ^ 2)) * restrictedDiff (fun u : ℝ => u) t))
  (h10 : 0 < x → x < 1 → originalPrimitives = negativePrimitives)
  : negativePrimitives = polynomialFamily := by
  sorry

/- Exercise 1984, gap 9
PROOF GAP @9
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}
5. sqrtn(2, 1 - x^{2}) = z
6. 0 < x ⇒ x < 1 ⇒ 0 < z
7. 0 < x ⇒ x < 1 ⇒ z < 1
8. 0 < x ⇒ x < 1 ⇒ x = sqrtn(2, 1 - z^{2})
9. 0 < x ⇒ x < 1 ⇒ diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . x) = -frac(z, sqrtn(2, 1 - z^{2})) * diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . z)
10. 0 < x ⇒ x < 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ∧ -1 < x ∧ x < 1 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(x^{5}, sqrtn(2, 1 - x^{2})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = (1 - z^{2})^{2} * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_4`(z) = -`F_3`(z)) }
11. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = (1 - z^{2})^{2} * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_6`(z) = -`F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ `F_7`(z) = -z + frac(2, 3) * z^{3} - frac(1, 5) * z^{5} + C) }

GOAL:
z = sqrtn(2, 1 - x^{2})

METHOD:

-/
theorem proof_gap_exercise_1984_9
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  (h5 : Real.sqrt (1 - x ^ 2) = z)
  (h6 : 0 < x → x < 1 → 0 < z)
  (h7 : 0 < x → x < 1 → z < 1)
  (h8 : 0 < x → x < 1 → x = Real.sqrt (1 - z ^ 2))
  (h9 : 0 < x → x < 1 → restrictedDiff (fun _ : ℝ => x) =
    (fun t => -(z / Real.sqrt (1 - z ^ 2)) * restrictedDiff (fun u : ℝ => u) t))
  (h10 : 0 < x → x < 1 → originalPrimitives = negativePrimitives)
  (h11 : negativePrimitives = polynomialFamily)
  : z = Real.sqrt (1 - x ^ 2) := by
  sorry

/- Exercise 1984, gap 10
PROOF GAP @10
ASSUM:
1. x ∈ RealSet ∧ -1 < x ∧ x < 1
2. z ∈ RealSet
3. C ∈ RealSet
4. frac(x^{5}, sqrtn(2, 1 - x^{2})) = x^{5} * (1 - x^{2})^{-frac(1, 2)}
5. sqrtn(2, 1 - x^{2}) = z
6. 0 < x ⇒ x < 1 ⇒ 0 < z
7. 0 < x ⇒ x < 1 ⇒ z < 1
8. 0 < x ⇒ x < 1 ⇒ x = sqrtn(2, 1 - z^{2})
9. 0 < x ⇒ x < 1 ⇒ diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . x) = -frac(z, sqrtn(2, 1 - z^{2})) * diff(fun z [z ∈ RealSet ∧ 0 < z ∧ z < 1] . z)
10. 0 < x ⇒ x < 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ∧ -1 < x ∧ x < 1 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(x^{5}, sqrtn(2, 1 - x^{2})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = (1 - z^{2})^{2} * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_4`(z) = -`F_3`(z)) }
11. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = (1 - z^{2})^{2} * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_6`(z) = -`F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ 0 < z ∧ z < 1 ⇒ `F_7`(z) = -z + frac(2, 3) * z^{3} - frac(1, 5) * z^{5} + C) }
12. z = sqrtn(2, 1 - x^{2})

GOAL:
{ `F_8` | forall (x), x ∈ RealSet ∧ -1 < x ∧ x < 1 ⇒ FunDeri(`F_8`, 1, 1)(x) = frac(x^{5}, sqrtn(2, 1 - x^{2})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_9` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ -1 < x ∧ x < 1 ⇒ `F_9`(x) = -sqrtn(2, 1 - x^{2}) + frac(2, 3) * sqrtn(2, 1 - x^{2})^{3} - frac(1, 5) * sqrtn(2, 1 - x^{2})^{5} + C) }

METHOD:

-/
theorem proof_gap_exercise_1984_10
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1)
  (h2 : z ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : x ^ 5 / Real.sqrt (1 - x ^ 2) = x ^ 5 * Real.rpow (1 - x ^ 2) (-(1 / 2 : ℝ)))
  (h5 : Real.sqrt (1 - x ^ 2) = z)
  (h6 : 0 < x → x < 1 → 0 < z)
  (h7 : 0 < x → x < 1 → z < 1)
  (h8 : 0 < x → x < 1 → x = Real.sqrt (1 - z ^ 2))
  (h9 : 0 < x → x < 1 → restrictedDiff (fun _ : ℝ => x) =
    (fun t => -(z / Real.sqrt (1 - z ^ 2)) * restrictedDiff (fun u : ℝ => u) t))
  (h10 : 0 < x → x < 1 → originalPrimitives = negativePrimitives)
  (h11 : negativePrimitives = polynomialFamily)
  (h12 : z = Real.sqrt (1 - x ^ 2))
  : originalPrimitives = answerFamily := by
  sorry

end Exercise1984
