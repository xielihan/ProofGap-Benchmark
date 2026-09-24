import Mathlib

-- exercise: exercise_1178
-- In one real independent variable, d^n f at x with increment dx is f^(n)(x) * dx^n.
-- Here y denotes the composite x ↦ log (u x), as explicitly stated in gap 1.
-- Preserve the literal FuncOfClassK definition from the theorem library, Thm 285.
-- Its n <= k clause is stronger than the usual C^k convention; see the review.
def exercise1178FuncOfClassK (f : ℝ → ℝ) (k : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ k → Differentiable ℝ (iteratedDeriv n f)) ∧
    Continuous (iteratedDeriv k f)

noncomputable def exercise1178Diff (n : ℕ) (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  iteratedDeriv n f x * dx ^ n

-- Exercise 1178, gap 1
-- SHA-256: 159762dec6a309f1f1036140ccf1c838512fa01fa6abfe6c18b39831a0637bf2
/-
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. FuncOfClassK(u, 3)
4. forall (x), x ∈ RealSet ⇒ u(x) > 0
5. forall (x), x ∈ RealSet ⇒ y(x) = ln(u(x))
GOAL:
diff(y) = frac(1, u) * diff(u)

METHOD:

-/
theorem proof_gap_exercise_1178_1
  (y u : ℝ → ℝ)
  (hu : exercise1178FuncOfClassK u 3)
  (hpos : ∀ x : ℝ, 0 < u x)
  (hy : ∀ x : ℝ, y x = Real.log (u x))
  : ∀ x dx : ℝ, exercise1178Diff 1 y x dx = (1 / u x) * exercise1178Diff 1 u x dx := by
  sorry

-- Exercise 1178, gap 2
-- SHA-256: 8835a8a0ce27a4f74586249e049d6fe9e0a7dff196ff32fe8e090c9a6b768aa3
/-
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet ∧ FuncOfClassK(u, 3)
3. y(u) = ln(u)
4. u > 0
5. diff(y) = frac(1, u) * diff(u)

GOAL:
diff^{2}(y) = -frac(1, u^{2}) * diff(u)^{2} + frac(1, u) * diff^{2}(u)

METHOD:

-/
theorem proof_gap_exercise_1178_2
  (y u : ℝ → ℝ)
  (hu : exercise1178FuncOfClassK u 3)
  (hy : ∀ x : ℝ, y x = Real.log (u x))
  (hpos : ∀ x : ℝ, 0 < u x)
  (hd1 : ∀ x dx : ℝ, exercise1178Diff 1 y x dx = (1 / u x) * exercise1178Diff 1 u x dx)
  : ∀ x dx : ℝ, exercise1178Diff 2 y x dx = -(1 / (u x) ^ 2) * (exercise1178Diff 1 u x dx) ^ 2
      + (1 / u x) * exercise1178Diff 2 u x dx := by
  sorry

-- Exercise 1178, gap 3
-- SHA-256: af7c3ceb4e3c215f8ad380021ea2683a94bd9aad3cea290d5a3580d668d82c59
/-
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet ∧ FuncOfClassK(u, 3)
3. y(u) = ln(u)
4. u > 0
5. diff(y) = frac(1, u) * diff(u)
6. diff^{2}(y) = -frac(1, u^{2}) * diff(u)^{2} + frac(1, u) * diff^{2}(u)

GOAL:
diff^{3}(y) = frac(2, u^{3}) * diff(u)^{3} - frac(2, u^{2}) * diff(u) * diff^{2}(u) - frac(1, u^{2}) * diff^{2}(u) * diff(u) + frac(1, u) * diff^{3}(u)

METHOD:

-/
theorem proof_gap_exercise_1178_3
  (y u : ℝ → ℝ)
  (hu : exercise1178FuncOfClassK u 3)
  (hy : ∀ x : ℝ, y x = Real.log (u x))
  (hpos : ∀ x : ℝ, 0 < u x)
  (hd1 : ∀ x dx : ℝ, exercise1178Diff 1 y x dx = (1 / u x) * exercise1178Diff 1 u x dx)
  (hd2 : ∀ x dx : ℝ, exercise1178Diff 2 y x dx = -(1 / (u x) ^ 2) * (exercise1178Diff 1 u x dx) ^ 2
      + (1 / u x) * exercise1178Diff 2 u x dx)
  : ∀ x dx : ℝ, exercise1178Diff 3 y x dx = (2 / (u x) ^ 3) * (exercise1178Diff 1 u x dx) ^ 3
      - (2 / (u x) ^ 2) * exercise1178Diff 1 u x dx * exercise1178Diff 2 u x dx
      - (1 / (u x) ^ 2) * exercise1178Diff 2 u x dx * exercise1178Diff 1 u x dx
      + (1 / u x) * exercise1178Diff 3 u x dx := by
  sorry

-- Exercise 1178, gap 4
-- SHA-256: ee2de811092ebe2b3e97ba4007cca495d3327c243a83793e81eee9b15e19ec34
/-
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet ∧ FuncOfClassK(u, 3)
3. y(u) = ln(u)
4. u > 0
5. diff(y) = frac(1, u) * diff(u)
6. diff^{2}(y) = -frac(1, u^{2}) * diff(u)^{2} + frac(1, u) * diff^{2}(u)
7. diff^{3}(y) = frac(2, u^{3}) * diff(u)^{3} - frac(2, u^{2}) * diff(u) * diff^{2}(u) - frac(1, u^{2}) * diff^{2}(u) * diff(u) + frac(1, u) * diff^{3}(u)

GOAL:
diff^{3}(y) = frac(2, u^{3}) * diff(u)^{3} - frac(3, u^{2}) * diff(u) * diff^{2}(u) + frac(1, u) * diff^{3}(u)

METHOD:

-/
theorem proof_gap_exercise_1178_4
  (y u : ℝ → ℝ)
  (hu : exercise1178FuncOfClassK u 3)
  (hy : ∀ x : ℝ, y x = Real.log (u x))
  (hpos : ∀ x : ℝ, 0 < u x)
  (hd1 : ∀ x dx : ℝ, exercise1178Diff 1 y x dx = (1 / u x) * exercise1178Diff 1 u x dx)
  (hd2 : ∀ x dx : ℝ, exercise1178Diff 2 y x dx = -(1 / (u x) ^ 2) * (exercise1178Diff 1 u x dx) ^ 2
      + (1 / u x) * exercise1178Diff 2 u x dx)
  (hd3 : ∀ x dx : ℝ, exercise1178Diff 3 y x dx = (2 / (u x) ^ 3) * (exercise1178Diff 1 u x dx) ^ 3
      - (2 / (u x) ^ 2) * exercise1178Diff 1 u x dx * exercise1178Diff 2 u x dx
      - (1 / (u x) ^ 2) * exercise1178Diff 2 u x dx * exercise1178Diff 1 u x dx
      + (1 / u x) * exercise1178Diff 3 u x dx)
  : ∀ x dx : ℝ, exercise1178Diff 3 y x dx = (2 / (u x) ^ 3) * (exercise1178Diff 1 u x dx) ^ 3
      - (3 / (u x) ^ 2) * exercise1178Diff 1 u x dx * exercise1178Diff 2 u x dx
      + (1 / u x) * exercise1178Diff 3 u x dx := by
  sorry

