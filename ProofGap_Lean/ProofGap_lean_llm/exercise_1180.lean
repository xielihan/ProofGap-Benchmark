import Mathlib

-- x and y are real-valued functions of an auxiliary real parameter t.
-- Successive differentials are represented by their coefficients (dt = 1).
-- No regularity hypotheses absent from the source gaps are added.
namespace Exercise1180

noncomputable def differential (n : ℕ) (u : ℝ → ℝ) : ℝ → ℝ :=
  iteratedDeriv n u

-- Iteration of (1 / x'(t)) d/dt, including on compound expressions.
noncomputable def relativeDerivative (u x : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => u
  | n + 1 => fun t => deriv (relativeDerivative u x n) t / deriv x t

noncomputable def secondFormula (x y : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (differential 1 x t * differential 2 y t -
    differential 1 y t * differential 2 x t) / (differential 1 x t) ^ 3

noncomputable def thirdFormula (x y : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (differential 1 x t *
      (differential 1 x t * differential 3 y t -
       differential 1 y t * differential 3 x t) -
    3 * differential 2 x t *
      (differential 1 x t * differential 2 y t -
       differential 1 y t * differential 2 x t)) / (differential 1 x t) ^ 5

end Exercise1180
open Exercise1180

/- Exercise 1180, gap 1
PROOF GAP @1
ASSUM:
1. x ∈ RealSet ∧ x ∈ Dom(f)
2. y ∈ RealSet
3. f : RealSet → RealSet
4. y = f(x)
5. diff(x) ≠ 0

GOAL:
FunDeri(y, x, 1) = FunDeri(y, x, 1)

METHOD:

-/
theorem proof_gap_exercise_1180_1
  (x y f : ℝ → ℝ) (t : ℝ)
  (h1 : x t ∈ (Set.univ : Set ℝ) ∧ x t ∈ {a | ∃ b, f a = b})
  (h2 : y t ∈ (Set.univ : Set ℝ))
  (h4 : y t = f (x t))
  (h5 : differential 1 x t ≠ 0)
  : relativeDerivative y x 1 t = relativeDerivative y x 1 t := by
  sorry

/- Exercise 1180, gap 2
PROOF GAP @2
ASSUM:
1. x ∈ RealSet ∧ x ∈ Dom(f)
2. y ∈ RealSet
3. f : RealSet → RealSet
4. y = f(x)
5. diff(x) ≠ 0
6. FunDeri(y, x, 1) = FunDeri(y, x, 1)

GOAL:
FunDeri(y, x, 2) = FunDeri(FunDeri(y, x, 1), x, 1)

METHOD:

-/
theorem proof_gap_exercise_1180_2
  (x y f : ℝ → ℝ) (t : ℝ)
  (h1 : x t ∈ (Set.univ : Set ℝ) ∧ x t ∈ {a | ∃ b, f a = b})
  (h2 : y t ∈ (Set.univ : Set ℝ))
  (h4 : y t = f (x t))
  (h5 : differential 1 x t ≠ 0)
  (h6 : relativeDerivative y x 1 t = relativeDerivative y x 1 t)
  : relativeDerivative y x 2 t = relativeDerivative (relativeDerivative y x 1) x 1 t := by
  sorry

/- Exercise 1180, gap 3
PROOF GAP @3
ASSUM:
1. x ∈ RealSet ∧ x ∈ Dom(f)
2. y ∈ RealSet
3. f : RealSet → RealSet
4. y = f(x)
5. diff(x) ≠ 0
6. FunDeri(y, x, 1) = FunDeri(y, x, 1)
7. FunDeri(y, x, 2) = FunDeri(FunDeri(y, x, 1), x, 1)

GOAL:
FunDeri(y, x, 2) = frac(diff(x) * diff^{2}(y) - diff(y) * diff^{2}(x), diff(x)^{3})

METHOD:

-/
theorem proof_gap_exercise_1180_3
  (x y f : ℝ → ℝ) (t : ℝ)
  (h1 : x t ∈ (Set.univ : Set ℝ) ∧ x t ∈ {a | ∃ b, f a = b})
  (h2 : y t ∈ (Set.univ : Set ℝ))
  (h4 : y t = f (x t))
  (h5 : differential 1 x t ≠ 0)
  (h6 : relativeDerivative y x 1 t = relativeDerivative y x 1 t)
  (h7 : relativeDerivative y x 2 t = relativeDerivative (relativeDerivative y x 1) x 1 t)
  : relativeDerivative y x 2 t = secondFormula x y t := by
  sorry

/- Exercise 1180, gap 4
PROOF GAP @4
ASSUM:
1. x ∈ RealSet ∧ x ∈ Dom(f)
2. y ∈ RealSet
3. f : RealSet → RealSet
4. y = f(x)
5. diff(x) ≠ 0
6. FunDeri(y, x, 1) = FunDeri(y, x, 1)
7. FunDeri(y, x, 2) = FunDeri(FunDeri(y, x, 1), x, 1)
8. FunDeri(y, x, 2) = frac(diff(x) * diff^{2}(y) - diff(y) * diff^{2}(x), diff(x)^{3})

GOAL:
FunDeri(y, x, 3) = FunDeri(frac(diff(x) * diff^{2}(y) - diff(y) * diff^{2}(x), diff(x)^{3}), x, 1)

METHOD:

-/
theorem proof_gap_exercise_1180_4
  (x y f : ℝ → ℝ) (t : ℝ)
  (h1 : x t ∈ (Set.univ : Set ℝ) ∧ x t ∈ {a | ∃ b, f a = b})
  (h2 : y t ∈ (Set.univ : Set ℝ))
  (h4 : y t = f (x t))
  (h5 : differential 1 x t ≠ 0)
  (h6 : relativeDerivative y x 1 t = relativeDerivative y x 1 t)
  (h7 : relativeDerivative y x 2 t = relativeDerivative (relativeDerivative y x 1) x 1 t)
  (h8 : relativeDerivative y x 2 t = secondFormula x y t)
  : relativeDerivative y x 3 t = relativeDerivative (secondFormula x y) x 1 t := by
  sorry

/- Exercise 1180, gap 5
PROOF GAP @5
ASSUM:
1. x ∈ RealSet ∧ x ∈ Dom(f)
2. y ∈ RealSet
3. f : RealSet → RealSet
4. y = f(x)
5. diff(x) ≠ 0
6. FunDeri(y, x, 1) = FunDeri(y, x, 1)
7. FunDeri(y, x, 2) = FunDeri(FunDeri(y, x, 1), x, 1)
8. FunDeri(y, x, 2) = frac(diff(x) * diff^{2}(y) - diff(y) * diff^{2}(x), diff(x)^{3})
9. FunDeri(y, x, 3) = FunDeri(frac(diff(x) * diff^{2}(y) - diff(y) * diff^{2}(x), diff(x)^{3}), x, 1)

GOAL:
FunDeri(y, x, 3) = frac(diff(x) * (diff(x) * diff^{3}(y) - diff(y) * diff^{3}(x)) - 3 * diff^{2}(x) * (diff(x) * diff^{2}(y) - diff(y) * diff^{2}(x)), diff(x)^{5})

METHOD:

-/
theorem proof_gap_exercise_1180_5
  (x y f : ℝ → ℝ) (t : ℝ)
  (h1 : x t ∈ (Set.univ : Set ℝ) ∧ x t ∈ {a | ∃ b, f a = b})
  (h2 : y t ∈ (Set.univ : Set ℝ))
  (h4 : y t = f (x t))
  (h5 : differential 1 x t ≠ 0)
  (h6 : relativeDerivative y x 1 t = relativeDerivative y x 1 t)
  (h7 : relativeDerivative y x 2 t = relativeDerivative (relativeDerivative y x 1) x 1 t)
  (h8 : relativeDerivative y x 2 t = secondFormula x y t)
  (h9 : relativeDerivative y x 3 t = relativeDerivative (secondFormula x y) x 1 t)
  : relativeDerivative y x 3 t = thirdFormula x y t := by
  sorry

