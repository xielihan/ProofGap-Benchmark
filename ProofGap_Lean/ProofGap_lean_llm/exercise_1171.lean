import Mathlib

-- exercise: exercise_1171
namespace Exercise1171

/-- The nth ordinary differential, evaluated at a base point x and an
independent real increment h: d^n f(x; h) = f^(n)(x) * h^n. -/
noncomputable def differential (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x h => iteratedDeriv n f x * h ^ n

/-- The first differential of the real coordinate function. -/
noncomputable def coordinateDifferential : ℝ → ℝ → ℝ :=
  differential 1 (fun x : ℝ => x)

end Exercise1171

open Exercise1171

-- Exercise 1171, gap 1
/-
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = x^{5}

GOAL:
diff^{5}(y) = 5! * diff(fun x [x ∈ RealSet] . x)^{5}

METHOD:

-/
theorem proof_gap_exercise_1171_1
  (y : ℝ → ℝ)
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x ^ (5 : ℕ))
  : differential 5 y =
    (fun x h : ℝ => (Nat.factorial 5 : ℝ) * (coordinateDifferential x h) ^ 5) := by
  sorry

-- Exercise 1171, gap 2
/-
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = x^{5}
3. diff^{5}(y) = 5! * diff(fun x [x ∈ RealSet] . x)^{5}

GOAL:
5! * diff(fun x [x ∈ RealSet] . x)^{5} = 120 * diff(fun x [x ∈ RealSet] . x)^{5}

METHOD:

-/
theorem proof_gap_exercise_1171_2
  (y : ℝ → ℝ)
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x ^ (5 : ℕ))
  (h1 : differential 5 y =
    (fun x h : ℝ => (Nat.factorial 5 : ℝ) * (coordinateDifferential x h) ^ 5))
  : (fun x h : ℝ => (Nat.factorial 5 : ℝ) * (coordinateDifferential x h) ^ 5) =
    (fun x h : ℝ => (120 : ℝ) * (coordinateDifferential x h) ^ 5) := by
  sorry

-- Exercise 1171, gap 3
/-
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ y(x) = x^{5}
3. diff^{5}(y) = 5! * diff(fun x [x ∈ RealSet] . x)^{5}
4. 5! * diff(fun x [x ∈ RealSet] . x)^{5} = 120 * diff(fun x [x ∈ RealSet] . x)^{5}

GOAL:
diff^{5}(y) = 120 * diff(fun x [x ∈ RealSet] . x)^{5}

METHOD:

-/
theorem proof_gap_exercise_1171_3
  (y : ℝ → ℝ)
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x ^ (5 : ℕ))
  (h1 : differential 5 y =
    (fun x h : ℝ => (Nat.factorial 5 : ℝ) * (coordinateDifferential x h) ^ 5))
  (h2 : (fun x h : ℝ => (Nat.factorial 5 : ℝ) * (coordinateDifferential x h) ^ 5) =
    (fun x h : ℝ => (120 : ℝ) * (coordinateDifferential x h) ^ 5))
  : differential 5 y =
    (fun x h : ℝ => (120 : ℝ) * (coordinateDifferential x h) ^ 5) := by
  sorry

