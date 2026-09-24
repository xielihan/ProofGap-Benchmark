import Mathlib

set_option linter.style.longLine false

/-!
Exercise 1983. Each source gap is copied verbatim immediately above its theorem.
The theorem proofs are intentionally left as `sorry`, as required by the worker task.
Source defects are retained; see reviews/exercise_1983.json.
-/

namespace Exercise1983

-- The real rational power with odd denominator, including negative inputs.
-- In the original text x^(2/3) means the real cube root of x^2.
noncomputable def twoThirdsPower (x : ℝ) : ℝ := Real.rpow |x| (2 / 3 : ℝ)

-- x^2 is nonnegative, so this rpow is precisely its nonnegative cube root.
noncomputable def substitution (x : ℝ) : ℝ :=
  Real.sqrt (1 + Real.rpow (x ^ 2) (1 / 3 : ℝ))

noncomputable def integrand (x : ℝ) : ℝ := x / substitution x

noncomputable def polynomial (z : ℝ) : ℝ :=
  (3 / 5 : ℝ) * z ^ 5 - 2 * z ^ 3 + 3 * z

-- A differential is a field of real continuous linear maps on its stated domain.
-- The lambda's bound variable does not turn the free parameter x into x(z).
noncomputable def restrictedDifferential (f : ℝ → ℝ) :
    {t : ℝ // t ≥ 1} → (ℝ →L[ℝ] ℝ) :=
  fun t => fderivWithin ℝ f (Set.Ici 1) t.val

-- FunDeri(F,1,1)(t)=v in an antiderivative family means the derivative
-- exists and equals v. HasDerivAt avoids accepting a nonexistent derivative
-- merely because Mathlib's total deriv assigns it the value zero.
def inputPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) →
    HasDerivAt F (integrand t * deriv (fun u : ℝ => u) t) t}

-- F3 is a total real function; only the explicitly restricted identity lambda
-- uses derivWithin. Both conjuncts remain under the same z ≥ 1 guard.
def scaledPrimitives : Set (ℝ → ℝ) :=
  {F4 | ∃ F3 : ℝ → ℝ, ∀ t : ℝ,
    t ∈ (Set.univ : Set ℝ) ∧ t ≥ 1 →
      HasDerivAt F3 ((t ^ 2 - 1) ^ 2 *
        derivWithin (fun u : ℝ => u) (Set.Ici 1) t) t ∧
      F4 t = 3 * F3 t}

def polynomialFamily : Set (ℝ → ℝ) :=
  {F | ∃ c : ℝ, c ∈ (Set.univ : Set ℝ) ∧
    ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 1 → F t = polynomial t + c}

def resultFamily : Set (ℝ → ℝ) :=
  {F | ∃ c : ℝ, c ∈ (Set.univ : Set ℝ) ∧
    ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → F t = polynomial (substitution t) + c}

end Exercise1983

open Exercise1983

-- Exercise 1983, gap 1
/-
PROOF GAP @1
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet

GOAL:
frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}

METHOD:

-/
theorem proof_gap_exercise_1983_1
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)) := by
  sorry

-- Exercise 1983, gap 2
/-
PROOF GAP @2
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet
4. frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}

GOAL:
1 + x^{frac(2, 3)} = z^{2}

METHOD:

-/
theorem proof_gap_exercise_1983_2
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)))
  : 1 + twoThirdsPower x = z ^ 2 := by
  sorry

-- Exercise 1983, gap 3
/-
PROOF GAP @3
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet
4. frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}
5. 1 + x^{frac(2, 3)} = z^{2}

GOAL:
z ≥ 1

METHOD:

-/
theorem proof_gap_exercise_1983_3
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)))
  (h5 : 1 + twoThirdsPower x = z ^ 2)
  : z ≥ 1 := by
  sorry

-- Exercise 1983, gap 4
/-
PROOF GAP @4
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet
4. frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}
5. 1 + x^{frac(2, 3)} = z^{2}
6. z ≥ 1

GOAL:
x ≥ 0 ⇒ z ≥ 1 ⇒ x = (z^{2} - 1)^{frac(3, 2)}

METHOD:

-/
theorem proof_gap_exercise_1983_4
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)))
  (h5 : 1 + twoThirdsPower x = z ^ 2)
  (h6 : z ≥ 1)
  : x ≥ 0 → z ≥ 1 → x = Real.rpow (z ^ 2 - 1) (3 / 2 : ℝ) := by
  sorry

-- Exercise 1983, gap 5
/-
PROOF GAP @5
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet
4. frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}
5. 1 + x^{frac(2, 3)} = z^{2}
6. z ≥ 1
7. x ≥ 0 ⇒ z ≥ 1 ⇒ x = (z^{2} - 1)^{frac(3, 2)}

GOAL:
x ≥ 0 ⇒ z ≥ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z ≥ 1] . x) = 3 * z * (z^{2} - 1)^{frac(1, 2)} * diff(fun z [z ∈ RealSet ∧ z ≥ 1] . z)

METHOD:

-/
theorem proof_gap_exercise_1983_5
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)))
  (h5 : 1 + twoThirdsPower x = z ^ 2)
  (h6 : z ≥ 1)
  (h7 : x ≥ 0 → z ≥ 1 → x = Real.rpow (z ^ 2 - 1) (3 / 2 : ℝ))
  : x ≥ 0 → z ≥ 1 →
    restrictedDifferential (fun _t : ℝ => x) =
      (3 * z * Real.rpow (z ^ 2 - 1) (1 / 2 : ℝ)) •
        restrictedDifferential (fun t : ℝ => t) := by
  sorry

-- Exercise 1983, gap 6
/-
PROOF GAP @6
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet
4. frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}
5. 1 + x^{frac(2, 3)} = z^{2}
6. z ≥ 1
7. x ≥ 0 ⇒ z ≥ 1 ⇒ x = (z^{2} - 1)^{frac(3, 2)}
8. x ≥ 0 ⇒ z ≥ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z ≥ 1] . x) = 3 * z * (z^{2} - 1)^{frac(1, 2)} * diff(fun z [z ∈ RealSet ∧ z ≥ 1] . z)

GOAL:
x ≥ 0 ⇒ z ≥ 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = (z^{2} - 1)^{2} * FunDeri(fun z [z ∈ RealSet ∧ z ≥ 1] . z, 1, 1)(z) ∧ `F_4`(z) = 3 * `F_3`(z)) }

METHOD:

-/
theorem proof_gap_exercise_1983_6
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)))
  (h5 : 1 + twoThirdsPower x = z ^ 2)
  (h6 : z ≥ 1)
  (h7 : x ≥ 0 → z ≥ 1 → x = Real.rpow (z ^ 2 - 1) (3 / 2 : ℝ))
  (h8 : x ≥ 0 → z ≥ 1 →
    restrictedDifferential (fun _t : ℝ => x) =
      (3 * z * Real.rpow (z ^ 2 - 1) (1 / 2 : ℝ)) •
        restrictedDifferential (fun t : ℝ => t))
  : x ≥ 0 → z ≥ 1 → inputPrimitives = scaledPrimitives := by
  sorry

-- Exercise 1983, gap 7
/-
PROOF GAP @7
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet
4. frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}
5. 1 + x^{frac(2, 3)} = z^{2}
6. z ≥ 1
7. x ≥ 0 ⇒ z ≥ 1 ⇒ x = (z^{2} - 1)^{frac(3, 2)}
8. x ≥ 0 ⇒ z ≥ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z ≥ 1] . x) = 3 * z * (z^{2} - 1)^{frac(1, 2)} * diff(fun z [z ∈ RealSet ∧ z ≥ 1] . z)
9. x ≥ 0 ⇒ z ≥ 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = (z^{2} - 1)^{2} * FunDeri(fun z [z ∈ RealSet ∧ z ≥ 1] . z, 1, 1)(z) ∧ `F_4`(z) = 3 * `F_3`(z)) }

GOAL:
{ `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = (z^{2} - 1)^{2} * FunDeri(fun z [z ∈ RealSet ∧ z ≥ 1] . z, 1, 1)(z) ∧ `F_6`(z) = 3 * `F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ `F_7`(z) = frac(3, 5) * z^{5} - 2 * z^{3} + 3 * z + C) }

METHOD:

-/
theorem proof_gap_exercise_1983_7
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)))
  (h5 : 1 + twoThirdsPower x = z ^ 2)
  (h6 : z ≥ 1)
  (h7 : x ≥ 0 → z ≥ 1 → x = Real.rpow (z ^ 2 - 1) (3 / 2 : ℝ))
  (h8 : x ≥ 0 → z ≥ 1 →
    restrictedDifferential (fun _t : ℝ => x) =
      (3 * z * Real.rpow (z ^ 2 - 1) (1 / 2 : ℝ)) •
        restrictedDifferential (fun t : ℝ => t))
  (h9 : x ≥ 0 → z ≥ 1 → inputPrimitives = scaledPrimitives)
  : scaledPrimitives = polynomialFamily := by
  sorry

-- Exercise 1983, gap 8
/-
PROOF GAP @8
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet
4. frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}
5. 1 + x^{frac(2, 3)} = z^{2}
6. z ≥ 1
7. x ≥ 0 ⇒ z ≥ 1 ⇒ x = (z^{2} - 1)^{frac(3, 2)}
8. x ≥ 0 ⇒ z ≥ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z ≥ 1] . x) = 3 * z * (z^{2} - 1)^{frac(1, 2)} * diff(fun z [z ∈ RealSet ∧ z ≥ 1] . z)
9. x ≥ 0 ⇒ z ≥ 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = (z^{2} - 1)^{2} * FunDeri(fun z [z ∈ RealSet ∧ z ≥ 1] . z, 1, 1)(z) ∧ `F_4`(z) = 3 * `F_3`(z)) }
10. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = (z^{2} - 1)^{2} * FunDeri(fun z [z ∈ RealSet ∧ z ≥ 1] . z, 1, 1)(z) ∧ `F_6`(z) = 3 * `F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ `F_7`(z) = frac(3, 5) * z^{5} - 2 * z^{3} + 3 * z + C) }

GOAL:
z = sqrtn(2, 1 + sqrtn(3, x^{2}))

METHOD:

-/
theorem proof_gap_exercise_1983_8
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)))
  (h5 : 1 + twoThirdsPower x = z ^ 2)
  (h6 : z ≥ 1)
  (h7 : x ≥ 0 → z ≥ 1 → x = Real.rpow (z ^ 2 - 1) (3 / 2 : ℝ))
  (h8 : x ≥ 0 → z ≥ 1 →
    restrictedDifferential (fun _t : ℝ => x) =
      (3 * z * Real.rpow (z ^ 2 - 1) (1 / 2 : ℝ)) •
        restrictedDifferential (fun t : ℝ => t))
  (h9 : x ≥ 0 → z ≥ 1 → inputPrimitives = scaledPrimitives)
  (h10 : scaledPrimitives = polynomialFamily)
  : z = substitution x := by
  sorry

-- Exercise 1983, gap 9
/-
PROOF GAP @9
ASSUM:
1. x ∈ RealSet
2. z ∈ RealSet ∧ z ≥ 1
3. C ∈ RealSet
4. frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) = x * (1 + x^{frac(2, 3)})^{-frac(1, 2)}
5. 1 + x^{frac(2, 3)} = z^{2}
6. z ≥ 1
7. x ≥ 0 ⇒ z ≥ 1 ⇒ x = (z^{2} - 1)^{frac(3, 2)}
8. x ≥ 0 ⇒ z ≥ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z ≥ 1] . x) = 3 * z * (z^{2} - 1)^{frac(1, 2)} * diff(fun z [z ∈ RealSet ∧ z ≥ 1] . z)
9. x ≥ 0 ⇒ z ≥ 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = (z^{2} - 1)^{2} * FunDeri(fun z [z ∈ RealSet ∧ z ≥ 1] . z, 1, 1)(z) ∧ `F_4`(z) = 3 * `F_3`(z)) }
10. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = (z^{2} - 1)^{2} * FunDeri(fun z [z ∈ RealSet ∧ z ≥ 1] . z, 1, 1)(z) ∧ `F_6`(z) = 3 * `F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ z ≥ 1 ⇒ `F_7`(z) = frac(3, 5) * z^{5} - 2 * z^{3} + 3 * z + C) }
11. z = sqrtn(2, 1 + sqrtn(3, x^{2}))

GOAL:
{ `F_8` | forall (x), x ∈ RealSet ⇒ FunDeri(`F_8`, 1, 1)(x) = frac(x, sqrtn(2, 1 + sqrtn(3, x^{2}))) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_9` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ⇒ `F_9`(x) = frac(3, 5) * sqrtn(2, 1 + sqrtn(3, x^{2}))^{5} - 2 * sqrtn(2, 1 + sqrtn(3, x^{2}))^{3} + 3 * sqrtn(2, 1 + sqrtn(3, x^{2})) + C) }

METHOD:

-/
theorem proof_gap_exercise_1983_9
  (x z C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : z ∈ (Set.univ : Set ℝ) ∧ z ≥ 1)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : integrand x = x * Real.rpow (1 + twoThirdsPower x) (-(1 / 2 : ℝ)))
  (h5 : 1 + twoThirdsPower x = z ^ 2)
  (h6 : z ≥ 1)
  (h7 : x ≥ 0 → z ≥ 1 → x = Real.rpow (z ^ 2 - 1) (3 / 2 : ℝ))
  (h8 : x ≥ 0 → z ≥ 1 →
    restrictedDifferential (fun _t : ℝ => x) =
      (3 * z * Real.rpow (z ^ 2 - 1) (1 / 2 : ℝ)) •
        restrictedDifferential (fun t : ℝ => t))
  (h9 : x ≥ 0 → z ≥ 1 → inputPrimitives = scaledPrimitives)
  (h10 : scaledPrimitives = polynomialFamily)
  (h11 : z = substitution x)
  : inputPrimitives = resultFamily := by
  sorry

