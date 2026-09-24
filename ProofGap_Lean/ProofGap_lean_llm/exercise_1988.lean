import Mathlib

noncomputable section
namespace Exercise1988

-- The real odd root, including negative radicands.
def fifthRoot (t : ℝ) : ℝ := Real.sign t * Real.rpow |t| (1 / 5 : ℝ)
-- Rational exponent -1/5 in the real odd-denominator convention.
def negFifthPower (t : ℝ) : ℝ := (fifthRoot t)⁻¹

def xDomain : Set ℝ := {x | x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ 1 + 1 / x ≠ 0}
def zDomain : Set ℝ := {z | z ∈ (Set.univ : Set ℝ) ∧ z ^ 5 ≠ 1}

def integrand (x : ℝ) : ℝ := 1 / (x ^ 3 * fifthRoot (1 + 1 / x))
def rewritePower (x : ℝ) : Prop :=
  integrand x = x ^ (-3 : ℤ) * negFifthPower (1 + x⁻¹)
def substitution (x z : ℝ) : Prop := 1 + x⁻¹ = z ^ 5
def inverseSubstitution (x z : ℝ) : Prop :=
  x ≠ 0 → z ^ 5 ≠ 1 → x = (z ^ 5 - 1)⁻¹

-- Preserve the literal constant lambda z ↦ x; do not substitute the inverse map.
-- In one dimension equality of differentials is equality of their dz coefficients.
def differentialStatement (x z : ℝ) : Prop :=
  x ≠ 0 → z ^ 5 ≠ 1 →
    derivWithin (fun _ : ℝ => x) zDomain z =
      -5 * z ^ 4 * (z ^ 5 - 1) ^ (-2 : ℤ) * deriv (fun t : ℝ => t) z

def originalPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ x : ℝ, x ∈ xDomain →
    deriv F x = integrand x * derivWithin (fun t : ℝ => t) xDomain x}
def scaledPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ z : ℝ, z ∈ zDomain →
    deriv G z = z ^ 3 * (z ^ 5 - 1) * deriv (fun t : ℝ => t) z ∧
    F z = -5 * G z}
def polynomialFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧ ∀ z : ℝ, z ∈ zDomain →
    F z = -(5 / 9 : ℝ) * z ^ 9 + (5 / 4 : ℝ) * z ^ 4 + C}
def finalFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧ ∀ x : ℝ, x ∈ xDomain →
    F x = -(5 / 9 : ℝ) * fifthRoot (1 + 1 / x) ^ 9 +
      (5 / 4 : ℝ) * fifthRoot (1 + 1 / x) ^ 4 + C}
def integralSubstitution (x z : ℝ) : Prop :=
  x ≠ 0 → z ^ 5 ≠ 1 → originalPrimitives = scaledPrimitives

end Exercise1988
open Exercise1988

/- Exercise 1988, gap 1
PROOF GAP @1
ASSUM:
1. x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0
2. z ∈ RealSet ∧ z^{5} ≠ 1
3. C ∈ RealSet

GOAL:
frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) = x^{-3} * (1 + x^{-1})^{-frac(1, 5)}

METHOD:

-/
theorem proof_gap_exercise_1988_1
  (x z C : ℝ)
  (h1 : x ∈ xDomain)
  (h2 : z ∈ zDomain)
  (h3 : C ∈ (Set.univ : Set ℝ))
  : rewritePower x := by
  sorry

/- Exercise 1988, gap 2
PROOF GAP @2
ASSUM:
1. x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0
2. z ∈ RealSet ∧ z^{5} ≠ 1
3. C ∈ RealSet
4. frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) = x^{-3} * (1 + x^{-1})^{-frac(1, 5)}

GOAL:
1 + x^{-1} = z^{5}

METHOD:

-/
theorem proof_gap_exercise_1988_2
  (x z C : ℝ)
  (h1 : x ∈ xDomain)
  (h2 : z ∈ zDomain)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : rewritePower x)
  : substitution x z := by
  sorry

/- Exercise 1988, gap 3
PROOF GAP @3
ASSUM:
1. x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0
2. z ∈ RealSet ∧ z^{5} ≠ 1
3. C ∈ RealSet
4. frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) = x^{-3} * (1 + x^{-1})^{-frac(1, 5)}
5. 1 + x^{-1} = z^{5}

GOAL:
x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ x = (z^{5} - 1)^{-1}

METHOD:

-/
theorem proof_gap_exercise_1988_3
  (x z C : ℝ)
  (h1 : x ∈ xDomain)
  (h2 : z ∈ zDomain)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : rewritePower x)
  (h5 : substitution x z)
  : inverseSubstitution x z := by
  sorry

/- Exercise 1988, gap 4
PROOF GAP @4
ASSUM:
1. x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0
2. z ∈ RealSet ∧ z^{5} ≠ 1
3. C ∈ RealSet
4. frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) = x^{-3} * (1 + x^{-1})^{-frac(1, 5)}
5. 1 + x^{-1} = z^{5}
6. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ x = (z^{5} - 1)^{-1}

GOAL:
x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z^{5} ≠ 1] . x) = -5 * z^{4} * (z^{5} - 1)^{-2} * diff(fun z [z ∈ RealSet] . z)

METHOD:

-/
theorem proof_gap_exercise_1988_4
  (x z C : ℝ)
  (h1 : x ∈ xDomain)
  (h2 : z ∈ zDomain)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : rewritePower x)
  (h5 : substitution x z)
  (h6 : inverseSubstitution x z)
  : differentialStatement x z := by
  sorry

/- Exercise 1988, gap 5
PROOF GAP @5
ASSUM:
1. x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0
2. z ∈ RealSet ∧ z^{5} ≠ 1
3. C ∈ RealSet
4. frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) = x^{-3} * (1 + x^{-1})^{-frac(1, 5)}
5. 1 + x^{-1} = z^{5}
6. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ x = (z^{5} - 1)^{-1}
7. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z^{5} ≠ 1] . x) = -5 * z^{4} * (z^{5} - 1)^{-2} * diff(fun z [z ∈ RealSet] . z)

GOAL:
x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) * FunDeri(fun x [x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = z^{3} * (z^{5} - 1) * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_4`(z) = -5 * `F_3`(z)) }

METHOD:

-/
theorem proof_gap_exercise_1988_5
  (x z C : ℝ)
  (h1 : x ∈ xDomain)
  (h2 : z ∈ zDomain)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : rewritePower x)
  (h5 : substitution x z)
  (h6 : inverseSubstitution x z)
  (h7 : differentialStatement x z)
  : integralSubstitution x z := by
  sorry

/- Exercise 1988, gap 6
PROOF GAP @6
ASSUM:
1. x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0
2. z ∈ RealSet ∧ z^{5} ≠ 1
3. C ∈ RealSet
4. frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) = x^{-3} * (1 + x^{-1})^{-frac(1, 5)}
5. 1 + x^{-1} = z^{5}
6. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ x = (z^{5} - 1)^{-1}
7. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z^{5} ≠ 1] . x) = -5 * z^{4} * (z^{5} - 1)^{-2} * diff(fun z [z ∈ RealSet] . z)
8. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) * FunDeri(fun x [x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = z^{3} * (z^{5} - 1) * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_4`(z) = -5 * `F_3`(z)) }

GOAL:
{ `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = z^{3} * (z^{5} - 1) * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_6`(z) = -5 * `F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ `F_7`(z) = -frac(5, 9) * z^{9} + frac(5, 4) * z^{4} + C) }

METHOD:

-/
theorem proof_gap_exercise_1988_6
  (x z C : ℝ)
  (h1 : x ∈ xDomain)
  (h2 : z ∈ zDomain)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : rewritePower x)
  (h5 : substitution x z)
  (h6 : inverseSubstitution x z)
  (h7 : differentialStatement x z)
  (h8 : integralSubstitution x z)
  : scaledPrimitives = polynomialFamily := by
  sorry

/- Exercise 1988, gap 7
PROOF GAP @7
ASSUM:
1. x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0
2. z ∈ RealSet ∧ z^{5} ≠ 1
3. C ∈ RealSet
4. frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) = x^{-3} * (1 + x^{-1})^{-frac(1, 5)}
5. 1 + x^{-1} = z^{5}
6. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ x = (z^{5} - 1)^{-1}
7. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z^{5} ≠ 1] . x) = -5 * z^{4} * (z^{5} - 1)^{-2} * diff(fun z [z ∈ RealSet] . z)
8. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) * FunDeri(fun x [x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = z^{3} * (z^{5} - 1) * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_4`(z) = -5 * `F_3`(z)) }
9. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = z^{3} * (z^{5} - 1) * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_6`(z) = -5 * `F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ `F_7`(z) = -frac(5, 9) * z^{9} + frac(5, 4) * z^{4} + C) }

GOAL:
z = sqrtn(5, 1 + frac(1, x))

METHOD:

-/
theorem proof_gap_exercise_1988_7
  (x z C : ℝ)
  (h1 : x ∈ xDomain)
  (h2 : z ∈ zDomain)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : rewritePower x)
  (h5 : substitution x z)
  (h6 : inverseSubstitution x z)
  (h7 : differentialStatement x z)
  (h8 : integralSubstitution x z)
  (h9 : scaledPrimitives = polynomialFamily)
  : z = fifthRoot (1 + 1 / x) := by
  sorry

/- Exercise 1988, gap 8
PROOF GAP @8
ASSUM:
1. x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0
2. z ∈ RealSet ∧ z^{5} ≠ 1
3. C ∈ RealSet
4. frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) = x^{-3} * (1 + x^{-1})^{-frac(1, 5)}
5. 1 + x^{-1} = z^{5}
6. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ x = (z^{5} - 1)^{-1}
7. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ diff(fun z [z ∈ RealSet ∧ z^{5} ≠ 1] . x) = -5 * z^{4} * (z^{5} - 1)^{-2} * diff(fun z [z ∈ RealSet] . z)
8. x ≠ 0 ⇒ z^{5} ≠ 1 ⇒ { `F_2` | forall (x), x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) * FunDeri(fun x [x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ FunDeri(`F_3`, 1, 1)(z) = z^{3} * (z^{5} - 1) * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_4`(z) = -5 * `F_3`(z)) }
9. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ FunDeri(`F_5`, 1, 1)(z) = z^{3} * (z^{5} - 1) * FunDeri(fun z [z ∈ RealSet] . z, 1, 1)(z) ∧ `F_6`(z) = -5 * `F_5`(z)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (z), z ∈ RealSet ∧ z^{5} ≠ 1 ⇒ `F_7`(z) = -frac(5, 9) * z^{9} + frac(5, 4) * z^{4} + C) }
10. z = sqrtn(5, 1 + frac(1, x))

GOAL:
{ `F_8` | forall (x), x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0 ⇒ FunDeri(`F_8`, 1, 1)(x) = frac(1, x^{3} * sqrtn(5, 1 + frac(1, x))) * FunDeri(fun x [x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0] . x, 1, 1)(x) } = { `F_9` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ≠ 0 ∧ 1 + frac(1, x) ≠ 0 ⇒ `F_9`(x) = -frac(5, 9) * sqrtn(5, 1 + frac(1, x))^{9} + frac(5, 4) * sqrtn(5, 1 + frac(1, x))^{4} + C) }

METHOD:

-/
theorem proof_gap_exercise_1988_8
  (x z C : ℝ)
  (h1 : x ∈ xDomain)
  (h2 : z ∈ zDomain)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : rewritePower x)
  (h5 : substitution x z)
  (h6 : inverseSubstitution x z)
  (h7 : differentialStatement x z)
  (h8 : integralSubstitution x z)
  (h9 : scaledPrimitives = polynomialFamily)
  (h10 : z = fifthRoot (1 + 1 / x))
  : originalPrimitives = finalFamily := by
  sorry

