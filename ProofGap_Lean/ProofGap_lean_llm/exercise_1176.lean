import Mathlib

open scoped BigOperators
set_option linter.unusedVariables false

namespace Exercise1176

-- Domain of the graph of the explicitly real-to-real function.
def domain (u : ℝ → ℝ) : Set ℝ := {x | ∃ z : ℝ, u x = z}

-- Literal expansion of the theorem library, Thm 286.
def classKOn (u : ℝ → ℝ) (I : Set ℝ) (k : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ k → DifferentiableOn ℝ (iteratedDerivWithin n u I) I) ∧
    ContinuousOn (iteratedDerivWithin k u I) I

-- The increment dx is independent; these are higher differentials, not just derivatives.
noncomputable def differential (n : ℕ) (u : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x dx => iteratedDeriv n u x * dx ^ n

noncomputable def restrictedDifferential (n : ℕ) (u : ℝ → ℝ) (I : Set ℝ) : ℝ → ℝ → ℝ :=
  fun x dx => iteratedDerivWithin n u I x * dx ^ n

noncomputable def leibniz (u : ℝ → ℝ) : ℝ → ℝ → ℝ := fun x dx =>
  ∑ i ∈ Finset.Icc (0 : ℕ) 10,
    (Nat.choose 10 i : ℝ) * differential (10 - i) u x dx * differential i u x dx

noncomputable def expanded (u : ℝ → ℝ) : ℝ → ℝ → ℝ := fun x dx =>
  u x * differential 10 u x dx +
  10 * differential 9 u x dx * differential 1 u x dx +
  (10 * 9 / (1 * 2) : ℝ) * differential 8 u x dx * differential 2 u x dx +
  (10 * 9 * 8 / (1 * 2 * 3) : ℝ) * differential 7 u x dx * differential 3 u x dx +
  (10 * 9 * 8 * 7 / (1 * 2 * 3 * 4) : ℝ) * differential 6 u x dx * differential 4 u x dx +
  (10 * 9 * 8 * 7 * 6 / (1 * 2 * 3 * 4 * 5) : ℝ) * (differential 5 u x dx) ^ 2 +
  (10 * 9 * 8 * 7 / (1 * 2 * 3 * 4) : ℝ) * differential 4 u x dx * differential 6 u x dx +
  (10 * 9 * 8 / (1 * 2 * 3) : ℝ) * differential 3 u x dx * differential 7 u x dx +
  (10 * 9 / (1 * 2) : ℝ) * differential 2 u x dx * differential 8 u x dx +
  10 * differential 1 u x dx * differential 9 u x dx + u x * differential 10 u x dx

noncomputable def collected (u : ℝ → ℝ) : ℝ → ℝ → ℝ := fun x dx =>
  2 * u x * differential 10 u x dx +
  20 * differential 1 u x dx * differential 9 u x dx +
  90 * differential 2 u x dx * differential 8 u x dx +
  240 * differential 3 u x dx * differential 7 u x dx +
  420 * differential 4 u x dx * differential 6 u x dx +
  252 * (differential 5 u x dx) ^ 2

end Exercise1176
open Exercise1176

/- Exercise 1176, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. I ⊆ RealSet
4. Dom(u) = I
5. FuncOfClassKOn(u, I, 10)
6. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x)^{2}
7. I = RealSet
GOAL:
diff^{10}(y) = diff^{10}(fun x [x ∈ RealSet ∧ x ∈ I] . u(x) * u(x))

METHOD:

-/
theorem proof_gap_exercise_1176_1
  (y u : ℝ → ℝ) (I : Set ℝ)
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : domain u = I)
  (h5 : classKOn u I 10)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x ^ 2)
  (h7 : I = (Set.univ : Set ℝ))
  : differential 10 y = restrictedDifferential 10 (fun x => u x * u x) I := by
  sorry

/- Exercise 1176, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. I ⊆ RealSet
4. Dom(u) = I
5. FuncOfClassKOn(u, I, 10)
6. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x)^{2}
7. diff^{10}(y) = diff^{10}(fun x [x ∈ RealSet ∧ x ∈ I] . u(x) * u(x))

GOAL:
diff^{10}(y) = sum_{ i = 0 }^{ 10 } (Combination(10, i) * diff^{10 - i}(u) * diff^{i}(u))

METHOD:

-/
theorem proof_gap_exercise_1176_2
  (y u : ℝ → ℝ) (I : Set ℝ)
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : domain u = I)
  (h5 : classKOn u I 10)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x ^ 2)
  (h7 : differential 10 y = restrictedDifferential 10 (fun x => u x * u x) I)
  : differential 10 y = leibniz u := by
  sorry

/- Exercise 1176, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. I ⊆ RealSet
4. Dom(u) = I
5. FuncOfClassKOn(u, I, 10)
6. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x)^{2}
7. diff^{10}(y) = diff^{10}(fun x [x ∈ RealSet ∧ x ∈ I] . u(x) * u(x))
8. diff^{10}(y) = sum_{ i = 0 }^{ 10 } (Combination(10, i) * diff^{10 - i}(u) * diff^{i}(u))

GOAL:
diff^{10}(y) = u * diff^{10}(u) + 10 * diff^{9}(u) * diff(u) + frac(10 * 9, 1 * 2) * diff^{8}(u) * diff^{2}(u) + frac(10 * 9 * 8, 1 * 2 * 3) * diff^{7}(u) * diff^{3}(u) + frac(10 * 9 * 8 * 7, 1 * 2 * 3 * 4) * diff^{6}(u) * diff^{4}(u) + frac(10 * 9 * 8 * 7 * 6, 1 * 2 * 3 * 4 * 5) * diff^{5}(u)^{2} + frac(10 * 9 * 8 * 7, 1 * 2 * 3 * 4) * diff^{4}(u) * diff^{6}(u) + frac(10 * 9 * 8, 1 * 2 * 3) * diff^{3}(u) * diff^{7}(u) + frac(10 * 9, 1 * 2) * diff^{2}(u) * diff^{8}(u) + 10 * diff(u) * diff^{9}(u) + u * diff^{10}(u)

METHOD:

-/
theorem proof_gap_exercise_1176_3
  (y u : ℝ → ℝ) (I : Set ℝ)
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : domain u = I)
  (h5 : classKOn u I 10)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x ^ 2)
  (h7 : differential 10 y = restrictedDifferential 10 (fun x => u x * u x) I)
  (h8 : differential 10 y = leibniz u)
  : differential 10 y = expanded u := by
  sorry

/- Exercise 1176, gap 4
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. I ⊆ RealSet
4. Dom(u) = I
5. FuncOfClassKOn(u, I, 10)
6. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x)^{2}
7. diff^{10}(y) = diff^{10}(fun x [x ∈ RealSet ∧ x ∈ I] . u(x) * u(x))
8. diff^{10}(y) = sum_{ i = 0 }^{ 10 } (Combination(10, i) * diff^{10 - i}(u) * diff^{i}(u))
9. diff^{10}(y) = u * diff^{10}(u) + 10 * diff^{9}(u) * diff(u) + frac(10 * 9, 1 * 2) * diff^{8}(u) * diff^{2}(u) + frac(10 * 9 * 8, 1 * 2 * 3) * diff^{7}(u) * diff^{3}(u) + frac(10 * 9 * 8 * 7, 1 * 2 * 3 * 4) * diff^{6}(u) * diff^{4}(u) + frac(10 * 9 * 8 * 7 * 6, 1 * 2 * 3 * 4 * 5) * diff^{5}(u)^{2} + frac(10 * 9 * 8 * 7, 1 * 2 * 3 * 4) * diff^{4}(u) * diff^{6}(u) + frac(10 * 9 * 8, 1 * 2 * 3) * diff^{3}(u) * diff^{7}(u) + frac(10 * 9, 1 * 2) * diff^{2}(u) * diff^{8}(u) + 10 * diff(u) * diff^{9}(u) + u * diff^{10}(u)

GOAL:
diff^{10}(y) = 2 * u * diff^{10}(u) + 20 * diff(u) * diff^{9}(u) + 90 * diff^{2}(u) * diff^{8}(u) + 240 * diff^{3}(u) * diff^{7}(u) + 420 * diff^{4}(u) * diff^{6}(u) + 252 * diff^{5}(u)^{2}

METHOD:

-/
theorem proof_gap_exercise_1176_4
  (y u : ℝ → ℝ) (I : Set ℝ)
  (h3 : I ⊆ (Set.univ : Set ℝ))
  (h4 : domain u = I)
  (h5 : classKOn u I 10)
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = u x ^ 2)
  (h7 : differential 10 y = restrictedDifferential 10 (fun x => u x * u x) I)
  (h8 : differential 10 y = leibniz u)
  (h9 : differential 10 y = expanded u)
  : differential 10 y = collected u := by
  sorry

