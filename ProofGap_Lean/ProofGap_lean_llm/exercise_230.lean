import Mathlib

namespace Exercise230

-- The three source cases partition ℝ; the final else is exactly the third case.
noncomputable def forward (x : ℝ) : ℝ :=
  if x < 1 then x else if x ≤ 4 then x ^ (2 : ℕ) else Real.rpow 2 x

noncomputable def backward (z : ℝ) : ℝ :=
  if z < 1 then z else if z ≤ 16 then Real.sqrt z else Real.logb 2 z

-- InverseFunc is the transposed graph (the theorem library, Thm 221).
def graph (f : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 = f p.1}

def inverseGraph (f : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 = f p.2}

end Exercise230

open Exercise230

-- Exercise 230, gap 1
/-
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. F : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = cases{ x if -∞ < x ∧ x < 1; x^{2} if 1 ≤ x ∧ x ≤ 4; 2^{x} if 4 < x ∧ x < +∞ }
4. forall (z), z ∈ RealSet ⇒ F(z) = cases{ z if -∞ < z ∧ z < 1; sqrtn(2, z) if 1 ≤ z ∧ z ≤ 16; log(2, z) if 16 < z ∧ z < +∞ }

GOAL:
F = InverseFunc(y)

METHOD:

-/
theorem proof_gap_exercise_230_1
  (y F : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = forward x)
  (h4 : ∀ z : ℝ, z ∈ (Set.univ : Set ℝ) → F z = backward z)
  : graph F = inverseGraph y := by
  sorry

-- Exercise 230, gap 2
/-
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. F : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = cases{ x if -∞ < x ∧ x < 1; x^{2} if 1 ≤ x ∧ x ≤ 4; 2^{x} if 4 < x ∧ x < +∞ }
4. F = InverseFunc(y)

GOAL:
forall (z), z ∈ RealSet ⇒ F(z) = cases{ z if -∞ < z ∧ z < 1; sqrtn(2, z) if 1 ≤ z ∧ z ≤ 16; log(2, z) if 16 < z ∧ z < +∞ }

METHOD:

-/
theorem proof_gap_exercise_230_2
  (y F : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = forward x)
  (h4 : graph F = inverseGraph y)
  : ∀ z : ℝ, z ∈ (Set.univ : Set ℝ) → F z = backward z := by
  sorry

-- Exercise 230, gap 3
/-
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. F : RealSet → RealSet
3. forall (x), x ∈ RealSet ⇒ y(x) = cases{ x if -∞ < x ∧ x < 1; x^{2} if 1 ≤ x ∧ x ≤ 4; 2^{x} if 4 < x ∧ x < +∞ }
4. F = InverseFunc(y)
5. forall (z), z ∈ RealSet ⇒ F(z) = cases{ z if -∞ < z ∧ z < 1; sqrtn(2, z) if 1 ≤ z ∧ z ≤ 16; log(2, z) if 16 < z ∧ z < +∞ }

GOAL:
(forall (z), z ∈ RealSet ⇒ F(z) = cases{ z if -∞ < z ∧ z < 1; sqrtn(2, z) if 1 ≤ z ∧ z ≤ 16; log(2, z) if 16 < z ∧ z < +∞ }) ⇒ F = InverseFunc(y)

METHOD:

-/
theorem proof_gap_exercise_230_3
  (y F : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = forward x)
  (h4 : graph F = inverseGraph y)
  (h5 : ∀ z : ℝ, z ∈ (Set.univ : Set ℝ) → F z = backward z)
  : (∀ z : ℝ, z ∈ (Set.univ : Set ℝ) → F z = backward z) →
      graph F = inverseGraph y := by
  sorry
