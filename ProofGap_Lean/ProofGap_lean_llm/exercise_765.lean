import Mathlib

set_option linter.style.longLine false

namespace Exercise765

-- The sign convention includes sgn(0) = 0 (source Thm 206).
noncomputable def sgn (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x = 0 then 0 else -1

-- Thms 220 and 221: the domain of the reversed graph is the range.
def inverseDomain (y : ℝ → ℝ) : Set ℝ := Set.range y

-- Only values on inverseDomain are used. The given y is strictly increasing,
-- so the chosen preimage is unique; off-domain values have no inverse meaning.
noncomputable def inverseValue (y : ℝ → ℝ) : ℝ → ℝ := Function.invFun y

-- Continuity of a partial inverse at points of S is relative to its own domain,
-- and requires those points to belong to that domain (Thms 267 and 268).
def inverseContinuousOn (y : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ t ∈ S, t ∈ inverseDomain y ∧
    ContinuousWithinAt (inverseValue y) (inverseDomain y) t

-- The source closed endpoints are intentionally preserved, including its error.
def closedDomain : Set ℝ := Set.Iic (-1) ∪ {0} ∪ Set.Ici 1
-- Gap 5 alone uses open endpoints.
def openDomain : Set ℝ := Set.Iio (-1) ∪ {0} ∪ Set.Ioi 1

-- On either displayed domain, the final else branch is exactly t = 0.
noncomputable def inverseFormula (t : ℝ) : ℝ :=
  if t ≥ 1 then Real.sqrt (t * sgn t - 1)
  else if t ≤ -1 then -Real.sqrt (t * sgn t - 1) else 0

end Exercise765

open Exercise765

/- Exercise 765, gap 1
SHA-256: 0c1df1e9ac23ab99f270c393fd464b67abf62330fe64212b4d9ced5c11b95387
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = (1 + x^{2}) * sgn(x)

GOAL:
forall (x), x ∈ RealSet ⇒ sgn(y(x)) = sgn(x)

METHOD:

-/
theorem proof_gap_exercise_765_1
  (y : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = (1 + x ^ (2 : ℕ)) * sgn x)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn (y x) = sgn x := by
  sorry

/- Exercise 765, gap 2
SHA-256: 40efa25a138de13b5d76ee3def074d7bfffa19fc988d9f0f69be23d916ef28b8
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = (1 + x^{2}) * sgn(x)
3. forall (x), x ∈ RealSet ⇒ sgn(y(x)) = sgn(x)

GOAL:
forall (x), x ∈ RealSet ⇒ sgn(x)^{2} = cases{ 1 if x ≠ 0; 0 if x = 0 }

METHOD:

-/
theorem proof_gap_exercise_765_2
  (y : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = (1 + x ^ (2 : ℕ)) * sgn x)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn (y x) = sgn x)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn x ^ (2 : ℕ) = if x ≠ 0 then 1 else 0 := by
  sorry

/- Exercise 765, gap 3
SHA-256: 1594d8365e79294b66503b3b3bbf91b17cc7b5cf711fa0218d2b60f90f95b9fd
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = (1 + x^{2}) * sgn(x)
3. forall (x), x ∈ RealSet ⇒ sgn(y(x)) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ sgn(x)^{2} = cases{ 1 if x ≠ 0; 0 if x = 0 }

GOAL:
forall (x), x ∈ RealSet ⇒ y(x) * sgn(y(x)) = (1 + x^{2}) * sgn(x)^{2}

METHOD:

-/
theorem proof_gap_exercise_765_3
  (y : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = (1 + x ^ (2 : ℕ)) * sgn x)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn (y x) = sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn x ^ (2 : ℕ) = if x ≠ 0 then 1 else 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x * sgn (y x) = (1 + x ^ (2 : ℕ)) * sgn x ^ (2 : ℕ) := by
  sorry

/- Exercise 765, gap 4
SHA-256: 5de3c1208d6c72067e978b04c0db3b62ab4f8046cc6bb081d96171eaa71dede7
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = (1 + x^{2}) * sgn(x)
3. forall (x), x ∈ RealSet ⇒ sgn(y(x)) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ sgn(x)^{2} = cases{ 1 if x ≠ 0; 0 if x = 0 }
5. forall (x), x ∈ RealSet ⇒ y(x) * sgn(y(x)) = (1 + x^{2}) * sgn(x)^{2}

GOAL:
Dom(InverseFunc(y)) = (-∞, -1] ∪ { 0 } ∪ [1, +∞)

METHOD:

-/
theorem proof_gap_exercise_765_4
  (y : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = (1 + x ^ (2 : ℕ)) * sgn x)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn (y x) = sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn x ^ (2 : ℕ) = if x ≠ 0 then 1 else 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x * sgn (y x) = (1 + x ^ (2 : ℕ)) * sgn x ^ (2 : ℕ))
  : inverseDomain y = closedDomain := by
  sorry

/- Exercise 765, gap 5
SHA-256: 5dbe7ca9dd5cccf053df4883706bf7c26b1107d14ba64a3edab321d16af2670e
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = (1 + x^{2}) * sgn(x)
3. forall (x), x ∈ RealSet ⇒ sgn(y(x)) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ sgn(x)^{2} = cases{ 1 if x ≠ 0; 0 if x = 0 }
5. forall (x), x ∈ RealSet ⇒ y(x) * sgn(y(x)) = (1 + x^{2}) * sgn(x)^{2}
6. Dom(InverseFunc(y)) = (-∞, -1) ∪ { 0 } ∪ (1, +∞)
GOAL:
forall (t), t ∈ RealSet ∧ t ∈ Dom(InverseFunc(y)) ⇒ InverseFunc(y, t) = cases{ sqrtn(2, t * sgn(t) - 1) if t ≥ 1; -sqrtn(2, t * sgn(t) - 1) if t ≤ -1; 0 if t = 0 }

METHOD:

-/
theorem proof_gap_exercise_765_5
  (y : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = (1 + x ^ (2 : ℕ)) * sgn x)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn (y x) = sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn x ^ (2 : ℕ) = if x ≠ 0 then 1 else 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x * sgn (y x) = (1 + x ^ (2 : ℕ)) * sgn x ^ (2 : ℕ))
  (h6 : inverseDomain y = openDomain)
  : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ inverseDomain y → inverseValue y t = inverseFormula t := by
  sorry

/- Exercise 765, gap 6
SHA-256: 0824cc9339ec9a55c251a03f13e8fda1ec5815511f037d62ccadf08d112334d0
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = (1 + x^{2}) * sgn(x)
3. forall (x), x ∈ RealSet ⇒ sgn(y(x)) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ sgn(x)^{2} = cases{ 1 if x ≠ 0; 0 if x = 0 }
5. forall (x), x ∈ RealSet ⇒ y(x) * sgn(y(x)) = (1 + x^{2}) * sgn(x)^{2}
6. Dom(InverseFunc(y)) = (-∞, -1] ∪ { 0 } ∪ [1, +∞)
7. forall (t), t ∈ RealSet ∧ t ∈ Dom(InverseFunc(y)) ⇒ InverseFunc(y, t) = cases{ sqrtn(2, t * sgn(t) - 1) if t ≥ 1; -sqrtn(2, t * sgn(t) - 1) if t ≤ -1; 0 if t = 0 }

GOAL:
ContinuousFuncOn(InverseFunc(y), (-∞, -1] ∪ { 0 } ∪ [1, +∞))

METHOD:

-/
theorem proof_gap_exercise_765_6
  (y : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = (1 + x ^ (2 : ℕ)) * sgn x)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn (y x) = sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn x ^ (2 : ℕ) = if x ≠ 0 then 1 else 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x * sgn (y x) = (1 + x ^ (2 : ℕ)) * sgn x ^ (2 : ℕ))
  (h6 : inverseDomain y = closedDomain)
  (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ inverseDomain y → inverseValue y t = inverseFormula t)
  : inverseContinuousOn y closedDomain := by
  sorry

/- Exercise 765, gap 7
SHA-256: ef518c6cf51a6800a0033b97d3b7251bb83de4ebd39377657c6e24d389b8e6c5
PROOF GAP @7
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = (1 + x^{2}) * sgn(x)
3. forall (x), x ∈ RealSet ⇒ sgn(y(x)) = sgn(x)
4. forall (x), x ∈ RealSet ⇒ sgn(x)^{2} = cases{ 1 if x ≠ 0; 0 if x = 0 }
5. forall (x), x ∈ RealSet ⇒ y(x) * sgn(y(x)) = (1 + x^{2}) * sgn(x)^{2}
6. Dom(InverseFunc(y)) = (-∞, -1] ∪ { 0 } ∪ [1, +∞)
7. forall (t), t ∈ RealSet ∧ t ∈ Dom(InverseFunc(y)) ⇒ InverseFunc(y, t) = cases{ sqrtn(2, t * sgn(t) - 1) if t ≥ 1; -sqrtn(2, t * sgn(t) - 1) if t ≤ -1; 0 if t = 0 }
8. ContinuousFuncOn(InverseFunc(y), (-∞, -1] ∪ { 0 } ∪ [1, +∞))

GOAL:
ContinuousFuncOn(InverseFunc(y), (-∞, -1] ∪ { 0 } ∪ [1, +∞))

METHOD:

-/
theorem proof_gap_exercise_765_7
  (y : ℝ → ℝ)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = (1 + x ^ (2 : ℕ)) * sgn x)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn (y x) = sgn x)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → sgn x ^ (2 : ℕ) = if x ≠ 0 then 1 else 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x * sgn (y x) = (1 + x ^ (2 : ℕ)) * sgn x ^ (2 : ℕ))
  (h6 : inverseDomain y = closedDomain)
  (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ inverseDomain y → inverseValue y t = inverseFormula t)
  (h8 : inverseContinuousOn y closedDomain)
  : inverseContinuousOn y closedDomain := by
  sorry

