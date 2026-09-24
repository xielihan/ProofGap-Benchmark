import Mathlib

-- All derivative evaluations below occur in the open domain (0, ∞).
-- The identity and sqrt are total representatives of the restricted source functions.
-- A differential is a continuous linear map at the current base point x.
namespace Exercise1680

noncomputable def differentialIdentity (x : ℝ) : Prop :=
  (1 / (Real.sqrt x * (1 + x))) • (fderiv ℝ (fun t : ℝ => t) x) =
    (2 : ℝ) • ((1 / (1 + (Real.sqrt x) ^ 2)) • (fderiv ℝ Real.sqrt x))

noncomputable def originalPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 →
    deriv F x = (1 / (Real.sqrt x * (1 + x))) * deriv (fun t : ℝ => t) x}

noncomputable def scaledPrimitives : Set (ℝ → ℝ) :=
  {F₄ | ∃ F₃ : ℝ → ℝ, ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 →
    deriv F₃ x = deriv Real.sqrt x / (1 + (Real.sqrt x) ^ 2) ∧
      F₄ x = 2 * F₃ x}

noncomputable def explicitPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, C ∈ (Set.univ : Set ℝ) ∧
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 →
      F x = 2 * Real.arctan (Real.sqrt x) + C}

end Exercise1680

open Exercise1680

/- Exercise 1680, gap 1
SHA-256: 073d56f9c4549c1e8f8922ac1c49b9e65d2b4f8f51755afd290865b4ddf6d994
PROOF GAP @1
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet

GOAL:
frac(diff(fun x [x ∈ RealSet ∧ x > 0] . x), sqrtn(2, x) * (1 + x)) = 2 * frac(diff(fun x [x ∈ RealSet ∧ x > 0] . sqrtn(2, x)), 1 + sqrtn(2, x)^{2})

METHOD:

-/
theorem proof_gap_exercise_1680_1
    (x C : ℝ)
    (h1 : x ∈ (Set.univ : Set ℝ) ∧ x > 0)
    (h2 : C ∈ (Set.univ : Set ℝ)) :
    differentialIdentity x := by
  sorry

/- Exercise 1680, gap 2
SHA-256: 19ddd6d81ea603ad7c34020f62a68c6786c332da5939f09415111bac4f2e7e28
PROOF GAP @2
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. frac(diff(fun x [x ∈ RealSet ∧ x > 0] . x), sqrtn(2, x) * (1 + x)) = 2 * frac(diff(fun x [x ∈ RealSet ∧ x > 0] . sqrtn(2, x)), 1 + sqrtn(2, x)^{2})

GOAL:
{ `F_2` | forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(2, x) * (1 + x)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet ∧ x > 0] . sqrtn(2, x), 1, 1)(x), 1 + sqrtn(2, x)^{2}) ∧ `F_4`(x) = 2 * `F_3`(x)) }

METHOD:

-/
theorem proof_gap_exercise_1680_2
    (x C : ℝ)
    (h1 : x ∈ (Set.univ : Set ℝ) ∧ x > 0)
    (h2 : C ∈ (Set.univ : Set ℝ))
    (h3 : differentialIdentity x) :
    originalPrimitives = scaledPrimitives := by
  sorry

/- Exercise 1680, gap 3
SHA-256: 400137237f0cdc767653267ed9229259a25cfebec07acd064b57097d8e130423
PROOF GAP @3
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. frac(diff(fun x [x ∈ RealSet ∧ x > 0] . x), sqrtn(2, x) * (1 + x)) = 2 * frac(diff(fun x [x ∈ RealSet ∧ x > 0] . sqrtn(2, x)), 1 + sqrtn(2, x)^{2})
4. { `F_2` | forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(2, x) * (1 + x)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet ∧ x > 0] . sqrtn(2, x), 1, 1)(x), 1 + sqrtn(2, x)^{2}) ∧ `F_4`(x) = 2 * `F_3`(x)) }

GOAL:
{ `F_5` | forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_5`, 1, 1)(x) = frac(1, sqrtn(2, x) * (1 + x)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . x, 1, 1)(x) } = { `F_6` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ `F_6`(x) = 2 * arctan(sqrtn(2, x)) + C) }

METHOD:

-/
theorem proof_gap_exercise_1680_3
    (x C : ℝ)
    (h1 : x ∈ (Set.univ : Set ℝ) ∧ x > 0)
    (h2 : C ∈ (Set.univ : Set ℝ))
    (h3 : differentialIdentity x)
    (h4 : originalPrimitives = scaledPrimitives) :
    originalPrimitives = explicitPrimitives := by
  sorry

