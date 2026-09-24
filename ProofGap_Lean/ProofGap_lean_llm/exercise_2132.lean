import Mathlib

set_option linter.style.longLine false

/- All functions are real-valued. Restrictions are retained by evaluating derivatives
within the open interval and imposing equalities only there. A one-dimensional
 differential is represented by its coefficient relative to dx.
The source only specifies t at the outer x; we do not globalize that assumption. -/
namespace Exercise2132

def domain : Set ℝ := Set.Ioo 0 1

noncomputable def root (u : ℝ) : ℝ := Real.sqrt (1 - u * Real.sqrt u)

noncomputable def coefficient (t : ℝ → ℝ) (u : ℝ) : ℝ :=
  -(4 / 3 : ℝ) * t u * Real.rpow (1 - t u ^ 2) (-(1 / 3 : ℝ))

-- Equality of the coefficients of the restricted differential forms.
def differentialIdentity (t : ℝ → ℝ) : Prop :=
  ∀ u ∈ domain,
    derivWithin (fun v : ℝ => v) domain u =
      coefficient t u * derivWithin t domain u

-- No constraint on any candidate primitive outside (0,1).
noncomputable def originalPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ u ∈ domain,
    deriv F u = Real.sqrt (u / (1 - u * Real.sqrt u)) *
      derivWithin (fun v : ℝ => v) domain u}

noncomputable def scaledPrimitives (t : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ u ∈ domain,
    deriv G u = derivWithin t domain u ∧ F u = -(4 / 3 : ℝ) * G u}

def translatedPrimitives (t : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, K ∈ (Set.univ : Set ℝ) ∧
    ∀ u ∈ domain, F u = -(4 / 3 : ℝ) * t u + K}

end Exercise2132

open Exercise2132

/- Exercise 2132, gap 1
SHA-256: 2d618990805cac818f82f3a1cf9d1bc8131e3d15593ea1efaf78024f632376b7
PROOF GAP @1
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. 0 < x
4. x < 1
5. t(x) = sqrtn(2, 1 - x * sqrtn(2, x))

GOAL:
0 < t(x)

METHOD:

-/
theorem proof_gap_exercise_2132_1
  (t : ℝ → ℝ) (x C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : 0 < x)
  (h4 : x < 1)
  (h5 : t x = root x)
  : 0 < t x := by
  sorry

/- Exercise 2132, gap 2
SHA-256: 5ac93d904b8a88a10c4fae57f9c9d75d076e8750952eaac2bc9b0f059943df1f
PROOF GAP @2
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. 0 < x
4. x < 1
5. t(x) = sqrtn(2, 1 - x * sqrtn(2, x))
6. 0 < t(x)

GOAL:
t(x) < 1

METHOD:

-/
theorem proof_gap_exercise_2132_2
  (t : ℝ → ℝ) (x C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : 0 < x)
  (h4 : x < 1)
  (h5 : t x = root x)
  (h6 : 0 < t x)
  : t x < 1 := by
  sorry

/- Exercise 2132, gap 3
SHA-256: 03d32b4a2fada54a5a1ba0a57be23672fe280b8b688ff35ed4fe167c6b5af540
PROOF GAP @3
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. 0 < x
4. x < 1
5. t(x) = sqrtn(2, 1 - x * sqrtn(2, x))
6. 0 < t(x)
7. t(x) < 1

GOAL:
x = (1 - t(x)^{2})^{frac(2, 3)}

METHOD:

-/
theorem proof_gap_exercise_2132_3
  (t : ℝ → ℝ) (x C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : 0 < x)
  (h4 : x < 1)
  (h5 : t x = root x)
  (h6 : 0 < t x)
  (h7 : t x < 1)
  : x = Real.rpow (1 - t x ^ 2) (2 / 3 : ℝ) := by
  sorry

/- Exercise 2132, gap 4
SHA-256: 1edc1a9b8d409ea96b40b3da4074146e9d3a8741b59d79b941584c038145d1bb
PROOF GAP @4
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. 0 < x
4. x < 1
5. t(x) = sqrtn(2, 1 - x * sqrtn(2, x))
6. 0 < t(x)
7. t(x) < 1
8. x = (1 - t(x)^{2})^{frac(2, 3)}

GOAL:
diff(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . x) = (fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . -frac(4, 3) * t(x) * (1 - t(x)^{2})^{-frac(1, 3)}) * diff(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x))

METHOD:

-/
theorem proof_gap_exercise_2132_4
  (t : ℝ → ℝ) (x C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : 0 < x)
  (h4 : x < 1)
  (h5 : t x = root x)
  (h6 : 0 < t x)
  (h7 : t x < 1)
  (h8 : x = Real.rpow (1 - t x ^ 2) (2 / 3 : ℝ))
  : differentialIdentity t := by
  sorry

/- Exercise 2132, gap 5
SHA-256: d29bad888f0d7140a875c575513df5b7426148c39130a351883ff92bbf7fd367
PROOF GAP @5
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. 0 < x
4. x < 1
5. t(x) = sqrtn(2, 1 - x * sqrtn(2, x))
6. 0 < t(x)
7. t(x) < 1
8. x = (1 - t(x)^{2})^{frac(2, 3)}
9. diff(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . x) = (fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . -frac(4, 3) * t(x) * (1 - t(x)^{2})^{-frac(1, 3)}) * diff(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x))

GOAL:
{ `F_2` | forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_2`, 1, 1)(x) = sqrtn(2, frac(x, 1 - x * sqrtn(2, x))) * FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_3`, 1, 1)(x) = FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x), 1, 1)(x) ∧ `F_4`(x) = -frac(4, 3) * `F_3`(x)) }

METHOD:

-/
theorem proof_gap_exercise_2132_5
  (t : ℝ → ℝ) (x C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : 0 < x)
  (h4 : x < 1)
  (h5 : t x = root x)
  (h6 : 0 < t x)
  (h7 : t x < 1)
  (h8 : x = Real.rpow (1 - t x ^ 2) (2 / 3 : ℝ))
  (h9 : differentialIdentity t)
  : originalPrimitives = scaledPrimitives t := by
  sorry

/- Exercise 2132, gap 6
SHA-256: 410e4e72817a4338a88f20658eda68df5b232b039acc39e79ae81c2459d0c05e
PROOF GAP @6
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. 0 < x
4. x < 1
5. t(x) = sqrtn(2, 1 - x * sqrtn(2, x))
6. 0 < t(x)
7. t(x) < 1
8. x = (1 - t(x)^{2})^{frac(2, 3)}
9. diff(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . x) = (fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . -frac(4, 3) * t(x) * (1 - t(x)^{2})^{-frac(1, 3)}) * diff(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x))
10. { `F_2` | forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_2`, 1, 1)(x) = sqrtn(2, frac(x, 1 - x * sqrtn(2, x))) * FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_3`, 1, 1)(x) = FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x), 1, 1)(x) ∧ `F_4`(x) = -frac(4, 3) * `F_3`(x)) }

GOAL:
{ `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_5`, 1, 1)(x) = FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x), 1, 1)(x) ∧ `F_6`(x) = -frac(4, 3) * `F_5`(x)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ `F_7`(x) = -frac(4, 3) * t(x) + C) }

METHOD:

-/
theorem proof_gap_exercise_2132_6
  (t : ℝ → ℝ) (x C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : 0 < x)
  (h4 : x < 1)
  (h5 : t x = root x)
  (h6 : 0 < t x)
  (h7 : t x < 1)
  (h8 : x = Real.rpow (1 - t x ^ 2) (2 / 3 : ℝ))
  (h9 : differentialIdentity t)
  (h10 : originalPrimitives = scaledPrimitives t)
  : scaledPrimitives t = translatedPrimitives t := by
  sorry

/- Exercise 2132, gap 7
SHA-256: 9d0cf307a59b6af00775afa618ab2d0aa3a25d9aa5e665712382cd41256a45be
PROOF GAP @7
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. 0 < x
4. x < 1
5. t(x) = sqrtn(2, 1 - x * sqrtn(2, x))
6. 0 < t(x)
7. t(x) < 1
8. x = (1 - t(x)^{2})^{frac(2, 3)}
9. diff(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . x) = (fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . -frac(4, 3) * t(x) * (1 - t(x)^{2})^{-frac(1, 3)}) * diff(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x))
10. { `F_2` | forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_2`, 1, 1)(x) = sqrtn(2, frac(x, 1 - x * sqrtn(2, x))) * FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_3`, 1, 1)(x) = FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x), 1, 1)(x) ∧ `F_4`(x) = -frac(4, 3) * `F_3`(x)) }
11. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_5`, 1, 1)(x) = FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . t(x), 1, 1)(x) ∧ `F_6`(x) = -frac(4, 3) * `F_5`(x)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ `F_7`(x) = -frac(4, 3) * t(x) + C) }

GOAL:
{ `F_8` | forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ FunDeri(`F_8`, 1, 1)(x) = sqrtn(2, frac(x, 1 - x * sqrtn(2, x))) * FunDeri(fun x [x ∈ RealSet ∧ 0 < x ∧ x < 1] . x, 1, 1)(x) } = { `F_9` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ⇒ `F_9`(x) = -frac(4, 3) * sqrtn(2, 1 - x * sqrtn(2, x)) + C) }

METHOD:

-/
theorem proof_gap_exercise_2132_7
  (t : ℝ → ℝ) (x C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : 0 < x)
  (h4 : x < 1)
  (h5 : t x = root x)
  (h6 : 0 < t x)
  (h7 : t x < 1)
  (h8 : x = Real.rpow (1 - t x ^ 2) (2 / 3 : ℝ))
  (h9 : differentialIdentity t)
  (h10 : originalPrimitives = scaledPrimitives t)
  (h11 : scaledPrimitives t = translatedPrimitives t)
  : originalPrimitives = translatedPrimitives root := by
  sorry

