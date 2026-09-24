import Mathlib

-- Literal expansion of the theorem library, Thm 286 (including n = k).
def exercise1121FuncOfClassKOn (f : ℝ → ℝ) (I : Set ℝ) (k : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ k → ∀ x ∈ I, DifferentiableAt ℝ (iteratedDeriv n f) x) ∧
    (∀ x ∈ I, ContinuousAt (iteratedDeriv k f) x)

/- Exercise 1121, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. I ⊆ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x)^{2}
5. FuncOfClassKOn(u, I, 2)
6. OpenSet(I)
GOAL:
forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 1)(x) = 2 * u(x) * FunDeri(u, 1, 1)(x)

METHOD:

-/
theorem proof_gap_exercise_1121_1
  (y u : ℝ → ℝ) (I : Set ℝ)
  (h_real : I ⊆ (Set.univ : Set ℝ))
  (h_square : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = (u x) ^ 2)
  (h_class : exercise1121FuncOfClassKOn u I 2)
  (h_open : IsOpen I)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I →
    iteratedDeriv 1 y x = 2 * u x * iteratedDeriv 1 u x := by
  sorry

/- Exercise 1121, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. I ⊆ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = u(x)^{2}
5. FuncOfClassKOn(u, I, 2)
6. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 1)(x) = 2 * u(x) * FunDeri(u, 1, 1)(x)
7. OpenSet(I)
GOAL:
forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 2)(x) = 2 * FunDeri(u, 1, 1)(x)^{2} + 2 * u(x) * FunDeri(u, 1, 2)(x) ∧ 2 * FunDeri(u, 1, 1)(x)^{2} + 2 * u(x) * FunDeri(u, 1, 2)(x) = 2 * (FunDeri(u, 1, 1)(x)^{2} + u(x) * FunDeri(u, 1, 2)(x))

METHOD:

-/
theorem proof_gap_exercise_1121_2
  (y u : ℝ → ℝ) (I : Set ℝ)
  (h_real : I ⊆ (Set.univ : Set ℝ))
  (h_square : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = (u x) ^ 2)
  (h_class : exercise1121FuncOfClassKOn u I 2)
  (h_first : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I →
    iteratedDeriv 1 y x = 2 * u x * iteratedDeriv 1 u x)
  (h_open : IsOpen I)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I →
    iteratedDeriv 2 y x =
      2 * (iteratedDeriv 1 u x) ^ 2 + 2 * u x * iteratedDeriv 2 u x ∧
    2 * (iteratedDeriv 1 u x) ^ 2 + 2 * u x * iteratedDeriv 2 u x =
      2 * ((iteratedDeriv 1 u x) ^ 2 + u x * iteratedDeriv 2 u x) := by
  sorry
