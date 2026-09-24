import Mathlib

-- Relations retain the source definitions of IsFunc and InverseFunc.
namespace Exercise763

def graph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | p.2 = f p.1}

def inverse (r : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | (p.2, p.1) ∈ r}

def isFunc (r : Set (ℝ × ℝ)) : Prop :=
  ∀ x y₁ y₂ : ℝ, (x, y₁) ∈ r → (x, y₂) ∈ r → y₁ = y₂

noncomputable def exampleFunction (x : ℝ) : ℝ := by
  classical
  exact if (∃ q : ℚ, (q : ℝ) = x) then x else -x

end Exercise763

open Exercise763

/- Exercise 763, gap 1
PROOF GAP @1
ASSUM:
1. f = (fun x [x ∈ RealSet] . cases{ x if x ∈ RationalSet; -x if x ∈ RealSet \ RationalSet })

GOAL:
IsFunc(f)

METHOD:

-/
theorem proof_gap_exercise_763_1
  (f : ℝ → ℝ)
  (h1 : f = exampleFunction)
  : isFunc (graph f) := by
  sorry

/- Exercise 763, gap 2
PROOF GAP @2
ASSUM:
1. f = (fun x [x ∈ RealSet] . cases{ x if x ∈ RationalSet; -x if x ∈ RealSet \ RationalSet })
2. IsFunc(f)

GOAL:
¬MonoIncFunc(f)

METHOD:

-/
theorem proof_gap_exercise_763_2
  (f : ℝ → ℝ)
  (h1 : f = exampleFunction)
  (h2 : isFunc (graph f))
  : ¬ Monotone f := by
  sorry

/- Exercise 763, gap 3
PROOF GAP @3
ASSUM:
1. f = (fun x [x ∈ RealSet] . cases{ x if x ∈ RationalSet; -x if x ∈ RealSet \ RationalSet })
2. IsFunc(f)
3. ¬MonoIncFunc(f)

GOAL:
¬MonoDecFunc(f)

METHOD:

-/
theorem proof_gap_exercise_763_3
  (f : ℝ → ℝ)
  (h1 : f = exampleFunction)
  (h2 : isFunc (graph f))
  (h3 : ¬ Monotone f)
  : ¬ Antitone f := by
  sorry

/- Exercise 763, gap 4
PROOF GAP @4
ASSUM:
1. f = (fun x [x ∈ RealSet] . cases{ x if x ∈ RationalSet; -x if x ∈ RealSet \ RationalSet })
2. IsFunc(f)
3. ¬MonoIncFunc(f)
4. ¬MonoDecFunc(f)

GOAL:
InverseFunc(f) = f

METHOD:

-/
theorem proof_gap_exercise_763_4
  (f : ℝ → ℝ)
  (h1 : f = exampleFunction)
  (h2 : isFunc (graph f))
  (h3 : ¬ Monotone f)
  (h4 : ¬ Antitone f)
  : inverse (graph f) = graph f := by
  sorry

/- Exercise 763, gap 5
PROOF GAP @5
ASSUM:
1. f = (fun x [x ∈ RealSet] . cases{ x if x ∈ RationalSet; -x if x ∈ RealSet \ RationalSet })
2. IsFunc(f)
3. ¬MonoIncFunc(f)
4. ¬MonoDecFunc(f)
5. InverseFunc(f) = f

GOAL:
IsFunc(InverseFunc(f))

METHOD:

-/
theorem proof_gap_exercise_763_5
  (f : ℝ → ℝ)
  (h1 : f = exampleFunction)
  (h2 : isFunc (graph f))
  (h3 : ¬ Monotone f)
  (h4 : ¬ Antitone f)
  (h5 : inverse (graph f) = graph f)
  : isFunc (inverse (graph f)) := by
  sorry

/- Exercise 763, gap 6
PROOF GAP @6
ASSUM:
1. f = (fun x [x ∈ RealSet] . cases{ x if x ∈ RationalSet; -x if x ∈ RealSet \ RationalSet })
2. IsFunc(f)
3. ¬MonoIncFunc(f)
4. ¬MonoDecFunc(f)
5. InverseFunc(f) = f
6. IsFunc(InverseFunc(f))

GOAL:
exists (f), f : RealSet → RealSet ∧ IsFunc(f) ∧ ¬MonoIncFunc(f) ∧ ¬MonoDecFunc(f) ∧ IsFunc(InverseFunc(f))

METHOD:

-/
theorem proof_gap_exercise_763_6
  (f : ℝ → ℝ)
  (h1 : f = exampleFunction)
  (h2 : isFunc (graph f))
  (h3 : ¬ Monotone f)
  (h4 : ¬ Antitone f)
  (h5 : inverse (graph f) = graph f)
  (h6 : isFunc (inverse (graph f)))
  : ∃ g : ℝ → ℝ, isFunc (graph g) ∧ ¬ Monotone g ∧ ¬ Antitone g ∧ isFunc (inverse (graph g)) := by
  sorry

/- Exercise 763, gap 7
PROOF GAP @7
ASSUM:
1. f = (fun x [x ∈ RealSet] . cases{ x if x ∈ RationalSet; -x if x ∈ RealSet \ RationalSet })
2. IsFunc(f)
3. ¬MonoIncFunc(f)
4. ¬MonoDecFunc(f)
5. InverseFunc(f) = f
6. IsFunc(InverseFunc(f))
7. exists (f), f : RealSet → RealSet ∧ IsFunc(f) ∧ ¬MonoIncFunc(f) ∧ ¬MonoDecFunc(f) ∧ IsFunc(InverseFunc(f))

GOAL:
exists (f), f : RealSet → RealSet ∧ IsFunc(f) ∧ ¬MonoIncFunc(f) ∧ ¬MonoDecFunc(f) ∧ IsFunc(InverseFunc(f))

METHOD:

-/
theorem proof_gap_exercise_763_7
  (f : ℝ → ℝ)
  (h1 : f = exampleFunction)
  (h2 : isFunc (graph f))
  (h3 : ¬ Monotone f)
  (h4 : ¬ Antitone f)
  (h5 : inverse (graph f) = graph f)
  (h6 : isFunc (inverse (graph f)))
  (h7 : ∃ g : ℝ → ℝ, isFunc (graph g) ∧ ¬ Monotone g ∧ ¬ Antitone g ∧ isFunc (inverse (graph g)))
  : ∃ g : ℝ → ℝ, isFunc (graph g) ∧ ¬ Monotone g ∧ ¬ Antitone g ∧ isFunc (inverse (graph g)) := by
  sorry

