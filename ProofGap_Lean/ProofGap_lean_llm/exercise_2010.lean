import Mathlib

noncomputable section
namespace Exercise2010

-- Signed real cube root, including negative arguments.
def cubeRoot (u : ℝ) : ℝ :=
  if 0 ≤ u then Real.rpow u (1 / 3 : ℝ)
  else -Real.rpow (-u) (1 / 3 : ℝ)

def domain : Set ℝ := {y | y ∈ (Set.univ : Set ℝ) ∧ Real.tan y ≠ 0}

-- Equality of differential fields on the common domain of the restricted lambdas.
def differentialIdentity (t : ℝ → ℝ) : Prop :=
  (fun y : domain => fderiv ℝ (fun z : ℝ => z) y.val) =
  (fun y : domain => (3 * t y.val ^ 2 / (1 + t y.val ^ 6)) •
    fderivWithin ℝ t domain y.val)

def originalPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ y ∈ domain, deriv F y = deriv (fun z : ℝ => z) y / cubeRoot (Real.tan y)}

def triplePrimitives (t : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ y ∈ domain,
    deriv G y = t y * derivWithin t domain y / (1 + t y ^ 6) ∧
    F y = 3 * G y}

def squarePrimitives (t : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ y ∈ domain,
    deriv G y = derivWithin (fun z => t z ^ 2) domain y / (1 + (t y ^ 2) ^ 3) ∧
    F y = (3 / 2 : ℝ) * G y}

def expression (u : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.log ((u ^ 2 + 1) ^ 2 / (u ^ 4 - u ^ 2 + 1)) +
    (Real.sqrt 3 / 2) * Real.arctan ((2 * u ^ 2 - 1) / Real.sqrt 3)

def explicitPrimitives (t : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, K ∈ (Set.univ : Set ℝ) ∧
    ∀ y ∈ domain, F y = expression (t y) + K}

end Exercise2010
open Exercise2010

/- Exercise 2010, gap 1
PROOF GAP @1
ASSUM:
1. x ∈ RealSet ∧ tan(x) ≠ 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. t(x) = sqrtn(3, tan(x))

GOAL:
t(x) ∈ RealSet

METHOD:

-/
theorem proof_gap_exercise_2010_1
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : x ∈ domain)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h4 : t x = cubeRoot (Real.tan x))
  : t x ∈ (Set.univ : Set ℝ) := by
  sorry

/- Exercise 2010, gap 2
PROOF GAP @2
ASSUM:
1. x ∈ RealSet ∧ tan(x) ≠ 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. t(x) = sqrtn(3, tan(x))
5. t(x) ∈ RealSet

GOAL:
t(x) ≠ 0

METHOD:

-/
theorem proof_gap_exercise_2010_2
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : x ∈ domain)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h4 : t x = cubeRoot (Real.tan x))
  (h5 : t x ∈ (Set.univ : Set ℝ))
  : t x ≠ 0 := by
  sorry

/- Exercise 2010, gap 3
PROOF GAP @3
ASSUM:
1. x ∈ RealSet ∧ tan(x) ≠ 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. t(x) = sqrtn(3, tan(x))
5. t(x) ∈ RealSet
6. t(x) ≠ 0

GOAL:
x = arctan(t(x)^{3})

METHOD:

-/
theorem proof_gap_exercise_2010_3
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : x ∈ domain)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h4 : t x = cubeRoot (Real.tan x))
  (h5 : t x ∈ (Set.univ : Set ℝ))
  (h6 : t x ≠ 0)
  : x = Real.arctan (t x ^ 3) := by
  sorry

/- Exercise 2010, gap 4
PROOF GAP @4
ASSUM:
1. x ∈ RealSet ∧ tan(x) ≠ 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. t(x) = sqrtn(3, tan(x))
5. t(x) ∈ RealSet
6. t(x) ≠ 0
7. x = arctan(t(x)^{3})

GOAL:
diff(fun x [x ∈ RealSet] . x) = (fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . frac(3 * t(x)^{2}, 1 + t(x)^{6})) * diff(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x))

METHOD:

-/
theorem proof_gap_exercise_2010_4
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : x ∈ domain)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h4 : t x = cubeRoot (Real.tan x))
  (h5 : t x ∈ (Set.univ : Set ℝ))
  (h6 : t x ≠ 0)
  (h7 : x = Real.arctan (t x ^ 3))
  : differentialIdentity t := by
  sorry

/- Exercise 2010, gap 5
PROOF GAP @5
ASSUM:
1. x ∈ RealSet ∧ tan(x) ≠ 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. t(x) = sqrtn(3, tan(x))
5. t(x) ∈ RealSet
6. t(x) ≠ 0
7. x = arctan(t(x)^{3})
8. diff(fun x [x ∈ RealSet] . x) = (fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . frac(3 * t(x)^{2}, 1 + t(x)^{6})) * diff(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x))

GOAL:
{ `F_2` | forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), sqrtn(3, tan(x))) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(t(x) * FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x), 1, 1)(x), 1 + t(x)^{6}) ∧ `F_4`(x) = 3 * `F_3`(x)) }

METHOD:

-/
theorem proof_gap_exercise_2010_5
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : x ∈ domain)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h4 : t x = cubeRoot (Real.tan x))
  (h5 : t x ∈ (Set.univ : Set ℝ))
  (h6 : t x ≠ 0)
  (h7 : x = Real.arctan (t x ^ 3))
  (h8 : differentialIdentity t)
  : originalPrimitives = triplePrimitives t := by
  sorry

/- Exercise 2010, gap 6
PROOF GAP @6
ASSUM:
1. x ∈ RealSet ∧ tan(x) ≠ 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. t(x) = sqrtn(3, tan(x))
5. t(x) ∈ RealSet
6. t(x) ≠ 0
7. x = arctan(t(x)^{3})
8. diff(fun x [x ∈ RealSet] . x) = (fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . frac(3 * t(x)^{2}, 1 + t(x)^{6})) * diff(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x))
9. { `F_2` | forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), sqrtn(3, tan(x))) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(t(x) * FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x), 1, 1)(x), 1 + t(x)^{6}) ∧ `F_4`(x) = 3 * `F_3`(x)) }

GOAL:
{ `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_5`, 1, 1)(x) = frac(t(x) * FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x), 1, 1)(x), 1 + t(x)^{6}) ∧ `F_6`(x) = 3 * `F_5`(x)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_7`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x)^{2}, 1, 1)(x), 1 + (t(x)^{2})^{3}) ∧ `F_8`(x) = frac(3, 2) * `F_7`(x)) }

METHOD:

-/
theorem proof_gap_exercise_2010_6
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : x ∈ domain)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h4 : t x = cubeRoot (Real.tan x))
  (h5 : t x ∈ (Set.univ : Set ℝ))
  (h6 : t x ≠ 0)
  (h7 : x = Real.arctan (t x ^ 3))
  (h8 : differentialIdentity t)
  (h9 : originalPrimitives = triplePrimitives t)
  : triplePrimitives t = squarePrimitives t := by
  sorry

/- Exercise 2010, gap 7
PROOF GAP @7
ASSUM:
1. x ∈ RealSet ∧ tan(x) ≠ 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. t(x) = sqrtn(3, tan(x))
5. t(x) ∈ RealSet
6. t(x) ≠ 0
7. x = arctan(t(x)^{3})
8. diff(fun x [x ∈ RealSet] . x) = (fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . frac(3 * t(x)^{2}, 1 + t(x)^{6})) * diff(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x))
9. { `F_2` | forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), sqrtn(3, tan(x))) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(t(x) * FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x), 1, 1)(x), 1 + t(x)^{6}) ∧ `F_4`(x) = 3 * `F_3`(x)) }
10. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_5`, 1, 1)(x) = frac(t(x) * FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x), 1, 1)(x), 1 + t(x)^{6}) ∧ `F_6`(x) = 3 * `F_5`(x)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_7`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x)^{2}, 1, 1)(x), 1 + (t(x)^{2})^{3}) ∧ `F_8`(x) = frac(3, 2) * `F_7`(x)) }

GOAL:
{ `F_10` | exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_9`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x)^{2}, 1, 1)(x), 1 + (t(x)^{2})^{3}) ∧ `F_10`(x) = frac(3, 2) * `F_9`(x)) } = { `F_11` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ `F_11`(x) = frac(1, 4) * ln(frac((t(x)^{2} + 1)^{2}, t(x)^{4} - t(x)^{2} + 1)) + frac(sqrtn(2, 3), 2) * arctan(frac(2 * t(x)^{2} - 1, sqrtn(2, 3))) + C) }

METHOD:

-/
theorem proof_gap_exercise_2010_7
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : x ∈ domain)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h4 : t x = cubeRoot (Real.tan x))
  (h5 : t x ∈ (Set.univ : Set ℝ))
  (h6 : t x ≠ 0)
  (h7 : x = Real.arctan (t x ^ 3))
  (h8 : differentialIdentity t)
  (h9 : originalPrimitives = triplePrimitives t)
  (h10 : triplePrimitives t = squarePrimitives t)
  : squarePrimitives t = explicitPrimitives t := by
  sorry

/- Exercise 2010, gap 8
PROOF GAP @8
ASSUM:
1. x ∈ RealSet ∧ tan(x) ≠ 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. t(x) = sqrtn(3, tan(x))
5. t(x) ∈ RealSet
6. t(x) ≠ 0
7. x = arctan(t(x)^{3})
8. diff(fun x [x ∈ RealSet] . x) = (fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . frac(3 * t(x)^{2}, 1 + t(x)^{6})) * diff(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x))
9. { `F_2` | forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), sqrtn(3, tan(x))) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(t(x) * FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x), 1, 1)(x), 1 + t(x)^{6}) ∧ `F_4`(x) = 3 * `F_3`(x)) }
10. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_5`, 1, 1)(x) = frac(t(x) * FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x), 1, 1)(x), 1 + t(x)^{6}) ∧ `F_6`(x) = 3 * `F_5`(x)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_7`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x)^{2}, 1, 1)(x), 1 + (t(x)^{2})^{3}) ∧ `F_8`(x) = frac(3, 2) * `F_7`(x)) }
11. { `F_10` | exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_9`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet ∧ tan(x) ≠ 0] . t(x)^{2}, 1, 1)(x), 1 + (t(x)^{2})^{3}) ∧ `F_10`(x) = frac(3, 2) * `F_9`(x)) } = { `F_11` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ `F_11`(x) = frac(1, 4) * ln(frac((t(x)^{2} + 1)^{2}, t(x)^{4} - t(x)^{2} + 1)) + frac(sqrtn(2, 3), 2) * arctan(frac(2 * t(x)^{2} - 1, sqrtn(2, 3))) + C) }

GOAL:
{ `F_12` | forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ FunDeri(`F_12`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), sqrtn(3, tan(x))) } = { `F_13` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ tan(x) ≠ 0 ⇒ `F_13`(x) = frac(1, 4) * ln(frac((sqrtn(3, tan(x))^{2} + 1)^{2}, sqrtn(3, tan(x))^{4} - sqrtn(3, tan(x))^{2} + 1)) + frac(sqrtn(2, 3), 2) * arctan(frac(2 * sqrtn(3, tan(x))^{2} - 1, sqrtn(2, 3))) + C) }

METHOD:

-/
theorem proof_gap_exercise_2010_8
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : x ∈ domain)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h4 : t x = cubeRoot (Real.tan x))
  (h5 : t x ∈ (Set.univ : Set ℝ))
  (h6 : t x ≠ 0)
  (h7 : x = Real.arctan (t x ^ 3))
  (h8 : differentialIdentity t)
  (h9 : originalPrimitives = triplePrimitives t)
  (h10 : triplePrimitives t = squarePrimitives t)
  (h11 : squarePrimitives t = explicitPrimitives t)
  : originalPrimitives = explicitPrimitives (fun y => cubeRoot (Real.tan y)) := by
  sorry

