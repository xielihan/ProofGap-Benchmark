import Mathlib

open scoped BigOperators

namespace Exercise2305

-- A derivative equality asserts existence of the ordinary first derivative.
-- The derivative of the identity in each source expression is 1.
def primitiveAt (F : ℝ → ℝ) (x : ℝ) : Prop :=
  HasDerivAt F ((⌊x⌋ : ℤ) : ℝ) x

def primitives : Set (ℝ → ℝ) :=
  {F | ∀ x : ℝ, 0 ≤ x → primitiveAt F x}

def shiftedPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∃ C : ℝ,
    ∀ x : ℝ, 0 ≤ x → primitiveAt G x ∧ F x = C + G x}

noncomputable def integralForm (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc (0 : ℤ) (⌊x⌋ - 1),
    ∫ t in (k : ℝ)..((k : ℝ) + 1), ((⌊t⌋ : ℤ) : ℝ)) +
  ∫ t in ((⌊x⌋ : ℤ) : ℝ)..x, ((⌊t⌋ : ℤ) : ℝ)

noncomputable def sumForm (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc (0 : ℤ) (⌊x⌋ - 1), (k : ℝ)) +
  ((⌊x⌋ : ℤ) : ℝ) * (x - ((⌊x⌋ : ℤ) : ℝ))

noncomputable def closedForm (x : ℝ) : ℝ :=
  x * ((⌊x⌋ : ℤ) : ℝ) -
    (((⌊x⌋ : ℤ) : ℝ) ^ 2 + ((⌊x⌋ : ℤ) : ℝ)) / 2

def translates (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → F x = f x + C}

def floorOnUnitIntervals : Prop :=
  ∀ t : ℝ, ∀ k : ℕ, (k : ℝ) ≤ t ∧ t < (k : ℝ) + 1 →
    (⌊t⌋ : ℤ) = (k : ℤ)

-- This condition concerns only the outer x, not the x bound in the sets.
def notPositiveInteger (x : ℝ) : Prop :=
  ¬ ∃ n : ℤ, 0 < n ∧ x = (n : ℝ)

/- Exercise 2305, gap 1
SHA-256: ab2faceec61b0de6e5b889774af78ea510e6e210bfaf63f9d5ed6bf00291d8e9
PROOF GAP @1
ASSUM:
1. x ∈ RealSet ∧ x ∈ NonNegRealSet
2. C ∈ RealSet

GOAL:
{ `F_2` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_5` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_3`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) ∧ `F_5`(x) = C + `F_3`(x))) }

METHOD:

-/
theorem proof_gap_exercise_2305_1
  (x C : ℝ)
  (h1 : 0 ≤ x)
  (h2 : C ∈ (Set.univ : Set ℝ))
  : primitives = shiftedPrimitives := by
  sorry

/- Exercise 2305, gap 2
SHA-256: 48f22169ce7404a40d90244ffe5d79162e6d8bc483e9b2a43affbb825fa0c01a
PROOF GAP @2
ASSUM:
1. x ∈ RealSet ∧ x ∈ NonNegRealSet
2. C ∈ RealSet
3. { `F_2` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_5` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_3`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) ∧ `F_5`(x) = C + `F_3`(x))) }
4. x ∉ PosIntegerSet

GOAL:
{ `F_6` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_6`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ `F_7`(x) = C + (sum_{ k = 0 }^{ floor(x) - 1 } (DefInt(k, k + 1, (fun t [t ∈ RealSet] . floor(t)) * diff(fun t [t ∈ RealSet] . t)))) + DefInt(floor(x), x, (fun t [t ∈ RealSet] . floor(t)) * diff(fun t [t ∈ RealSet] . t))) }

METHOD:

-/
theorem proof_gap_exercise_2305_2
  (x C : ℝ)
  (h1 : 0 ≤ x)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : primitives = shiftedPrimitives)
  (h4 : notPositiveInteger x)
  : primitives = translates integralForm := by
  sorry

/- Exercise 2305, gap 3
SHA-256: 601e0362a5a1abbd82ee2e0f31fc71cd7b982866daad1797bb651b23513ebc31
PROOF GAP @3
ASSUM:
1. x ∈ RealSet ∧ x ∈ NonNegRealSet
2. C ∈ RealSet
3. { `F_2` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_5` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_3`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) ∧ `F_5`(x) = C + `F_3`(x))) }
4. { `F_6` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_6`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ `F_7`(x) = C + (sum_{ k = 0 }^{ floor(x) - 1 } (DefInt(k, k + 1, (fun t [t ∈ RealSet] . floor(t)) * diff(fun t [t ∈ RealSet] . t)))) + DefInt(floor(x), x, (fun t [t ∈ RealSet] . floor(t)) * diff(fun t [t ∈ RealSet] . t))) }

GOAL:
forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ NonNegIntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)

METHOD:

-/
theorem proof_gap_exercise_2305_3
  (x C : ℝ)
  (h1 : 0 ≤ x)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : primitives = shiftedPrimitives)
  (h4 : primitives = translates integralForm)
  : floorOnUnitIntervals := by
  sorry

/- Exercise 2305, gap 4
SHA-256: 24fc0175b1a232993a48045be9069e0a52fec012e76b0cecb31176a7d633bf22
PROOF GAP @4
ASSUM:
1. x ∈ RealSet ∧ x ∈ NonNegRealSet
2. C ∈ RealSet
3. { `F_2` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_5` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_3`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) ∧ `F_5`(x) = C + `F_3`(x))) }
4. { `F_6` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_6`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ `F_7`(x) = C + (sum_{ k = 0 }^{ floor(x) - 1 } (DefInt(k, k + 1, (fun t [t ∈ RealSet] . floor(t)) * diff(fun t [t ∈ RealSet] . t)))) + DefInt(floor(x), x, (fun t [t ∈ RealSet] . floor(t)) * diff(fun t [t ∈ RealSet] . t))) }
5. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ NonNegIntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)
6. x ∉ PosIntegerSet

GOAL:
{ `F_8` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_8`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_9` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ `F_9`(x) = C + (sum_{ k = 0 }^{ floor(x) - 1 } (k)) + floor(x) * (x - floor(x))) }

METHOD:

-/
theorem proof_gap_exercise_2305_4
  (x C : ℝ)
  (h1 : 0 ≤ x)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : primitives = shiftedPrimitives)
  (h4 : primitives = translates integralForm)
  (h5 : floorOnUnitIntervals)
  (h6 : notPositiveInteger x)
  : primitives = translates sumForm := by
  sorry

/- Exercise 2305, gap 5
SHA-256: de555f75d7fa2493d8aa1051bba3aa63becf2ad28d8e63852cde30f624d8e293
PROOF GAP @5
ASSUM:
1. x ∈ RealSet ∧ x ∈ NonNegRealSet
2. C ∈ RealSet
3. { `F_2` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_2`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_5` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_3`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) ∧ `F_5`(x) = C + `F_3`(x))) }
4. { `F_6` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_6`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ `F_7`(x) = C + (sum_{ k = 0 }^{ floor(x) - 1 } (DefInt(k, k + 1, (fun t [t ∈ RealSet] . floor(t)) * diff(fun t [t ∈ RealSet] . t)))) + DefInt(floor(x), x, (fun t [t ∈ RealSet] . floor(t)) * diff(fun t [t ∈ RealSet] . t))) }
5. forall (t), t ∈ RealSet ⇒ (forall (k), k ∈ NonNegIntegerSet ∧ k ≤ t ∧ t < k + 1 ⇒ floor(t) = k)
6. { `F_8` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_8`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_9` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ `F_9`(x) = C + (sum_{ k = 0 }^{ floor(x) - 1 } (k)) + floor(x) * (x - floor(x))) }
7. x ∉ PosIntegerSet

GOAL:
{ `F_10` | forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ FunDeri(`F_10`, 1, 1)(x) = floor(x) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_11` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ∈ NonNegRealSet ⇒ `F_11`(x) = x * floor(x) - frac(floor(x)^{2} + floor(x), 2) + C) }

METHOD:

-/
theorem proof_gap_exercise_2305_5
  (x C : ℝ)
  (h1 : 0 ≤ x)
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : primitives = shiftedPrimitives)
  (h4 : primitives = translates integralForm)
  (h5 : floorOnUnitIntervals)
  (h6 : primitives = translates sumForm)
  (h7 : notPositiveInteger x)
  : primitives = translates closedForm := by
  sorry

end Exercise2305
