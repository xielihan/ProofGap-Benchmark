import Mathlib

-- exercise: exercise_1134_1
-- Literal expansion of the theorem library, Thms 267, 276, 286.
-- The source uses n <= k (including differentiability of the kth derivative).
def exercise1134ClassOn (f : ℝ → ℝ) (I : Set ℝ) (k : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ k → ∀ x ∈ I, DifferentiableAt ℝ (iteratedDeriv n f) x) ∧
  (∀ x ∈ I, ContinuousAt (iteratedDeriv k f) x)

-- In one independent real variable, d^n f at increment h is f^(n)(x) h^n.
-- Products of differentials below are ordinary symmetric products, not wedge products.
noncomputable def exercise1134Diff (n : ℕ) (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  iteratedDeriv n f x * h ^ n

/- Exercise 1134_1, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. I ⊆ RealSet
5. FuncOfClassKOn(u, I, 2)
6. FuncOfClassKOn(v, I, 2)
7. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x) * v(x)
8. I = RealSet
GOAL:
diff(y) = u * diff(v) + v * diff(u)

METHOD:

-/
theorem proof_gap_exercise_1134_1_1
  (y u v : ℝ → ℝ) (I : Set ℝ)
  (h4 : I ⊆ (Set.univ : Set ℝ))
  (h5 : exercise1134ClassOn u I 2)
  (h6 : exercise1134ClassOn v I 2)
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x * v x)
  (h8 : I = (Set.univ : Set ℝ))
  : exercise1134Diff 1 y =
    (fun x h => u x * exercise1134Diff 1 v x h + v x * exercise1134Diff 1 u x h) := by
  sorry

/- Exercise 1134_1, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. I ⊆ RealSet
5. FuncOfClassKOn(u, I, 2)
6. FuncOfClassKOn(v, I, 2)
7. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x) * v(x)
8. diff(y) = u * diff(v) + v * diff(u)

GOAL:
diff^{2}(y) = diff(u) * diff(v) + u * diff^{2}(v) + diff(v) * diff(u) + v * diff^{2}(u)

METHOD:

-/
theorem proof_gap_exercise_1134_1_2
  (y u v : ℝ → ℝ) (I : Set ℝ)
  (h4 : I ⊆ (Set.univ : Set ℝ))
  (h5 : exercise1134ClassOn u I 2)
  (h6 : exercise1134ClassOn v I 2)
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x * v x)
  (h8 : exercise1134Diff 1 y =
    (fun x h => u x * exercise1134Diff 1 v x h + v x * exercise1134Diff 1 u x h))
  : exercise1134Diff 2 y =
    (fun x h => exercise1134Diff 1 u x h * exercise1134Diff 1 v x h +
      u x * exercise1134Diff 2 v x h +
      exercise1134Diff 1 v x h * exercise1134Diff 1 u x h +
      v x * exercise1134Diff 2 u x h) := by
  sorry

/- Exercise 1134_1, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. I ⊆ RealSet
5. FuncOfClassKOn(u, I, 2)
6. FuncOfClassKOn(v, I, 2)
7. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x) * v(x)
8. diff(y) = u * diff(v) + v * diff(u)
9. diff^{2}(y) = diff(u) * diff(v) + u * diff^{2}(v) + diff(v) * diff(u) + v * diff^{2}(u)

GOAL:
diff^{2}(y) = u * diff^{2}(v) + 2 * diff(u) * diff(v) + v * diff^{2}(u)

METHOD:

-/
theorem proof_gap_exercise_1134_1_3
  (y u v : ℝ → ℝ) (I : Set ℝ)
  (h4 : I ⊆ (Set.univ : Set ℝ))
  (h5 : exercise1134ClassOn u I 2)
  (h6 : exercise1134ClassOn v I 2)
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x * v x)
  (h8 : exercise1134Diff 1 y =
    (fun x h => u x * exercise1134Diff 1 v x h + v x * exercise1134Diff 1 u x h))
  (h9 : exercise1134Diff 2 y =
    (fun x h => exercise1134Diff 1 u x h * exercise1134Diff 1 v x h +
      u x * exercise1134Diff 2 v x h +
      exercise1134Diff 1 v x h * exercise1134Diff 1 u x h +
      v x * exercise1134Diff 2 u x h))
  : exercise1134Diff 2 y =
    (fun x h => u x * exercise1134Diff 2 v x h +
      2 * exercise1134Diff 1 u x h * exercise1134Diff 1 v x h +
      v x * exercise1134Diff 2 u x h) := by
  sorry

