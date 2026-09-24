import Mathlib

-- exercise: exercise_1173
namespace Exercise1173

-- The nth ordinary differential at x, evaluated on a real increment h.
-- This is the one-variable symmetric differential, not an exterior power.
noncomputable def differential (n : ℕ) (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  iteratedDeriv n f x * h ^ n

-- Literal definition from the theorem library, Thm 285.
-- Its inclusive upper bound is stronger than the usual C^k convention.
def sourceFuncOfClassK (f : ℝ → ℝ) (k : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ k → Differentiable ℝ (iteratedDeriv n f)) ∧
    Continuous (iteratedDeriv k f)

/- Exercise 1173, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = x * cos(2 * x)

GOAL:
forall (x), x ∈ RealSet ⇒ diff^{10}(y) = FunDeri(fun x [x ∈ RealSet] . x * cos(2 * x), 1, 10)(x) * diff(fun x [x ∈ RealSet] . x)^{10}

METHOD:
-/
theorem proof_gap_exercise_1173_1
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x * Real.cos (2 * x))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ h : ℝ,
    differential 10 y x h =
      iteratedDeriv 10 (fun t : ℝ => t * Real.cos (2 * t)) x *
        (differential 1 (fun t : ℝ => t) x h) ^ 10 := by
  sorry

/- Exercise 1173, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = x * cos(2 * x)
3. FuncOfClassK(y, 10)
GOAL:
diff^{10}(y) = (fun x [x ∈ RealSet] . 2^{10} * x * cos(2 * x + frac(10 * π, 2)) + 10 * 2^{9} * cos(2 * x + frac(9 * π, 2))) * diff(fun x [x ∈ RealSet] . x)^{10}

METHOD:
-/
theorem proof_gap_exercise_1173_2
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x * Real.cos (2 * x))
  (h2 : sourceFuncOfClassK y 10)
  : differential 10 y =
    (fun x h : ℝ =>
      ((2 : ℝ) ^ 10 * x * Real.cos (2 * x + 10 * Real.pi / 2) +
        10 * (2 : ℝ) ^ 9 * Real.cos (2 * x + 9 * Real.pi / 2)) *
          (differential 1 (fun t : ℝ => t) x h) ^ 10) := by
  sorry

/- Exercise 1173, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = x * cos(2 * x)
3. forall (x), x ∈ RealSet ⇒ diff^{10}(y) = FunDeri(fun x [x ∈ RealSet] . x * cos(2 * x), 1, 10)(x) * diff(fun x [x ∈ RealSet] . x)^{10}
4. diff^{10}(y) = (fun x [x ∈ RealSet] . 2^{10} * x * cos(2 * x + frac(10 * π, 2)) + 10 * 2^{9} * cos(2 * x + frac(9 * π, 2))) * diff(fun x [x ∈ RealSet] . x)^{10}

GOAL:
diff^{10}(y) = (fun x [x ∈ RealSet] . -1024 * (x * cos(2 * x) + 5 * sin(2 * x))) * diff(fun x [x ∈ RealSet] . x)^{10}

METHOD:
-/
theorem proof_gap_exercise_1173_3
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x * Real.cos (2 * x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ h : ℝ,
    differential 10 y x h =
      iteratedDeriv 10 (fun t : ℝ => t * Real.cos (2 * t)) x *
        (differential 1 (fun t : ℝ => t) x h) ^ 10)
  (h3 : differential 10 y =
    (fun x h : ℝ =>
      ((2 : ℝ) ^ 10 * x * Real.cos (2 * x + 10 * Real.pi / 2) +
        10 * (2 : ℝ) ^ 9 * Real.cos (2 * x + 9 * Real.pi / 2)) *
          (differential 1 (fun t : ℝ => t) x h) ^ 10))
  : differential 10 y =
    (fun x h : ℝ =>
      (-1024 * (x * Real.cos (2 * x) + 5 * Real.sin (2 * x))) *
        (differential 1 (fun t : ℝ => t) x h) ^ 10) := by
  sorry

end Exercise1173
