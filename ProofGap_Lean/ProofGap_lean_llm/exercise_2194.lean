import Mathlib

open scoped BigOperators Topology
open Filter
namespace Exercise2194

-- Definitions follow the theorem library 206, 227, 255, 268.
def boundedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ t ∈ s, |f t| ≤ M

noncomputable def oscillation (f : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ s, ∃ v ∈ s, r = |f u - f v|}

-- Riemann integrability via the bounded-function Darboux mesh criterion.
-- Icc a b is empty when b < a; no reversal of the source interval.
def riemannOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  boundedOn f (Set.Icc a b) ∧
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (m : ℕ) (p : ℕ → ℝ), 0 < m → p 0 = a → p m = b →
      (∀ j < m, p j < p (j + 1)) →
      (∀ j < m, p (j + 1) - p j < δ) →
      (∑ j ∈ Finset.range m,
        oscillation f (Set.Icc (p j) (p (j + 1))) * (p (j + 1) - p j)) < ε

-- Integer indices are converted only in contexts where they are nonnegative.
def atIndex (x : ℕ → ℝ) (j : ℤ) : ℝ := x j.toNat

def partitionConditions (x : ℕ → ℝ) (dx : ℤ → ℝ) (d δ : ℝ) (m : ℕ) : Prop :=
  0 < m ∧ 0 < m ∧
  (∀ j : ℤ, 0 ≤ j ∧ j ≤ (m : ℤ) - 1 →
    dx j = atIndex x (j + 1) - atIndex x j) ∧
  x 0 = 0 ∧ x m = 1 ∧
  (∀ j : ℤ, 0 ≤ j ∧ j ≤ (m : ℤ) - 1 → atIndex x j < atIndex x (j + 1)) ∧
  d < δ

noncomputable def weightedSum (ω dx : ℤ → ℝ) (a b : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc a b, ω j * dx j

noncomputable def widthSum (dx : ℤ → ℝ) (a b : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc a b, dx j

/-
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet

GOAL:
BoundedFuncOn(f, [0, 1])

METHOD:

-/
-- Exercise 2194, gap 1
theorem proof_gap_exercise_2194_1
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  : boundedOn f (Set.Icc 0 1) := by
  sorry

/-
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })

METHOD:

-/
-- Exercise 2194, gap 2
theorem proof_gap_exercise_2194_2
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}) := by
  sorry

/-
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })

GOAL:
forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2

METHOD:

-/
-- Exercise 2194, gap 3
theorem proof_gap_exercise_2194_3
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2 := by
  sorry

/-
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })

METHOD:

-/
-- Exercise 2194, gap 4
theorem proof_gap_exercise_2194_4
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t} := by
  sorry

/-
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])

METHOD:

-/
-- Exercise 2194, gap 5
theorem proof_gap_exercise_2194_5
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1 := by
  sorry

/-
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))

METHOD:

-/
-- Exercise 2194, gap 6
theorem proof_gap_exercise_2194_6
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5) := by
  sorry

/-
PROOF GAP @7
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))

METHOD:

-/
-- Exercise 2194, gap 7
theorem proof_gap_exercise_2194_7
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5 := by
  sorry

/-
PROOF GAP @8
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))

METHOD:

-/
-- Exercise 2194, gap 8
theorem proof_gap_exercise_2194_8
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1) := by
  sorry

/-
PROOF GAP @9
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))

METHOD:

-/
-- Exercise 2194, gap 9
theorem proof_gap_exercise_2194_9
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5 := by
  sorry

/-
PROOF GAP @10
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))

METHOD:

-/
-- Exercise 2194, gap 10
theorem proof_gap_exercise_2194_10
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀ := by
  sorry

/-
PROOF GAP @11
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))

METHOD:

-/
-- Exercise 2194, gap 11
theorem proof_gap_exercise_2194_11
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5) := by
  sorry

/-
PROOF GAP @12
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))
25. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * frac(2 * ε, 5) = frac(4 * ε, 5))

METHOD:

-/
-- Exercise 2194, gap 12
theorem proof_gap_exercise_2194_12
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  (h25 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5))
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * (2 * ε / 5) = 4 * ε / 5 := by
  sorry

/-
PROOF GAP @13
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))
25. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))
26. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * frac(2 * ε, 5) = frac(4 * ε, 5))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) < frac(4 * ε, 5))

METHOD:

-/
-- Exercise 2194, gap 13
theorem proof_gap_exercise_2194_13
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  (h25 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5))
  (h26 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * (2 * ε / 5) = 4 * ε / 5)
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ < 4 * ε / 5 := by
  sorry

/-
PROOF GAP @14
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))
25. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))
26. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * frac(2 * ε, 5) = frac(4 * ε, 5))
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) < frac(4 * ε, 5))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) = (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))))

METHOD:

-/
-- Exercise 2194, gap 14
theorem proof_gap_exercise_2194_14
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  (h25 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5))
  (h26 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * (2 * ε / 5) = 4 * ε / 5)
  (h27 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ < 4 * ε / 5)
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) = weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) := by
  sorry

/-
PROOF GAP @15
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))
25. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))
26. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * frac(2 * ε, 5) = frac(4 * ε, 5))
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) < frac(4 * ε, 5))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) = (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))) < ε)

METHOD:

-/
-- Exercise 2194, gap 15
theorem proof_gap_exercise_2194_15
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  (h25 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5))
  (h26 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * (2 * ε / 5) = 4 * ε / 5)
  (h27 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ < 4 * ε / 5)
  (h28 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) = weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1))
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε := by
  sorry

/-
PROOF GAP @16
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))
25. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))
26. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * frac(2 * ε, 5) = frac(4 * ε, 5))
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) < frac(4 * ε, 5))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) = (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))) < ε)

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < ε)

METHOD:

-/
-- Exercise 2194, gap 16
theorem proof_gap_exercise_2194_16
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  (h25 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5))
  (h26 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * (2 * ε / 5) = 4 * ε / 5)
  (h27 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ < 4 * ε / 5)
  (h28 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) = weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1))
  (h29 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε)
  : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) < ε := by
  sorry

/-
PROOF GAP @17
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))
25. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))
26. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * frac(2 * ε, 5) = frac(4 * ε, 5))
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) < frac(4 * ε, 5))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) = (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))) < ε)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < ε)

GOAL:
lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i))) = 0

METHOD:

-/
-- Exercise 2194, gap 17
theorem proof_gap_exercise_2194_17
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  (h25 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5))
  (h26 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * (2 * ε / 5) = 4 * ε / 5)
  (h27 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ < 4 * ε / 5)
  (h28 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) = weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1))
  (h29 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε)
  (h30 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) < ε)
  : Tendsto (fun (_d : ℝ) => weightedSum ω dx 0 ((n : ℤ) - 1)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry

/-
PROOF GAP @18
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))
25. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))
26. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * frac(2 * ε, 5) = frac(4 * ε, 5))
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) < frac(4 * ε, 5))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) = (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))) < ε)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < ε)
31. lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i))) = 0

GOAL:
IntegrableFuncOn(f, [0, 1])

METHOD:

-/
-- Exercise 2194, gap 18
theorem proof_gap_exercise_2194_18
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  (h25 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5))
  (h26 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * (2 * ε / 5) = 4 * ε / 5)
  (h27 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ < 4 * ε / 5)
  (h28 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) = weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1))
  (h29 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε)
  (h30 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) < ε)
  (h31 : Tendsto (fun (_d : ℝ) => weightedSum ω dx 0 ((n : ℤ) - 1)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  : riemannOn f 0 1 := by
  sorry

/-
PROOF GAP @19
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. Δx : IntegerSet → RealSet
4. ω : IntegerSet → RealSet
5. d ∈ RealSet ∧ d > 0
6. n ∈ NonNegIntegerSet ∧ n > 0
7. i ∈ IntegerSet
8. i_{0} ∈ IntegerSet ∧ 0 ≤ i_{0} ∧ i_{0} ≤ n - 1
9. δ ∈ RealSet ∧ δ > 0
10. η ∈ RealSet ∧ η > 0
11. forall (x), x ∈ RealSet ∧ 0 < x ∧ x ≤ 1 ⇒ f(x) = sgn(sin(frac(π, x)))
12. f(0) ∈ RealSet
13. BoundedFuncOn(f, [0, 1])
14. forall (x), x ∈ RealSet ∧ x ∈ [0, 1] ⇒ (¬ContinuousFuncAt(f, x) ⇔ x ∈ { 0 } ∪ { frac(1, n) | n ∈ PosIntegerSet })
15. forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ 0 ≤ α ∧ α < β ∧ β ≤ 1 ⇒ OscillationOn(f, [α, β]) ≤ 2
16. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ FiniteSet({ x | x ∈ [frac(ε, 5), 1], ¬ContinuousFuncAt(f, x) })
17. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ IntegrableFuncOn(f, [frac(ε, 5), 1])
18. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (η), η ∈ RealSet ∧ η > 0 ∧ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ [α, β] ⊆ [frac(ε, 5), 1] ∧ d < η ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5)))
19. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ δ = min(frac(ε, 5), η)
20. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ i_{0} = max({ i | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 ∧ x(i) ≤ frac(ε, 5) }))
21. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ x(i_{0}) ≤ frac(ε, 5))
22. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ frac(ε, 5) < x(i_{0} + 1))
23. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i)) < frac(ε, 5))
24. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) ≤ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))))
25. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * (sum_{ i = 0 }^{ i_{0} } (Δx(i))) < 2 * frac(2 * ε, 5))
26. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ 2 * frac(2 * ε, 5) = frac(4 * ε, 5))
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i)) < frac(4 * ε, 5))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) = (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ (sum_{ i = 0 }^{ i_{0} } (ω(i) * Δx(i))) + (sum_{ i = i_{0} + 1 }^{ n - 1 } (ω(i) * Δx(i))) < ε)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)) ∧ x(0) = 0 ∧ x(n) = 1 ∧ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)) ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i)) < ε)
31. lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (ω(i) * Δx(i))) = 0
32. IntegrableFuncOn(f, [0, 1])

GOAL:
IntegrableFuncOn(f, [0, 1])

METHOD:

-/
-- Exercise 2194, gap 19
theorem proof_gap_exercise_2194_19
  (f : ℝ → ℝ) (x : ℕ → ℝ) (dx ω : ℤ → ℝ)
  (d : ℝ) (n : ℕ) (i i₀ : ℤ) (δ η : ℝ)
  (h5 : 0 < d) (h6 : 0 < n)
  (h8 : 0 ≤ i₀ ∧ i₀ ≤ (n : ℤ) - 1)
  (h9 : 0 < δ) (h10 : 0 < η)
  (h11 : ∀ t : ℝ, 0 < t ∧ t ≤ 1 → f t = Real.sign (Real.sin (Real.pi / t)))
  (h12 : f 0 ∈ (Set.univ : Set ℝ))
  (h13 : boundedOn f (Set.Icc 0 1))
  (h14 : ∀ t : ℝ, t ∈ Set.Icc 0 1 → (¬ ContinuousAt f t ↔ t ∈ ({0} : Set ℝ) ∪ {r | ∃ k : ℤ, 0 < k ∧ r = 1 / (k : ℝ)}))
  (h15 : ∀ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 → oscillation f (Set.Icc α β) ≤ 2)
  (h16 : ∀ ε : ℝ, 0 < ε → Set.Finite {t : ℝ | t ∈ Set.Icc (ε / 5) 1 ∧ ¬ ContinuousAt f t})
  (h17 : ∀ ε : ℝ, 0 < ε → riemannOn f (ε / 5) 1)
  (h18 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (∀ α β : ℝ, Set.Icc α β ⊆ Set.Icc (ε / 5) 1 ∧ d < η → weightedSum ω dx 0 ((n : ℤ) - 1) < ε / 5))
  (h19 : ∀ ε : ℝ, 0 < ε → δ = min (ε / 5) η)
  (h20 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → IsGreatest {j : ℤ | 0 ≤ j ∧ j ≤ (m : ℤ) - 1 ∧ atIndex x j ≤ ε / 5} i₀)
  (h21 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → atIndex x i₀ ≤ ε / 5)
  (h22 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → ε / 5 < atIndex x (i₀ + 1))
  (h23 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε / 5)
  (h24 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ ≤ 2 * widthSum dx 0 i₀)
  (h25 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * widthSum dx 0 i₀ < 2 * (2 * ε / 5))
  (h26 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → 2 * (2 * ε / 5) = 4 * ε / 5)
  (h27 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ < 4 * ε / 5)
  (h28 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) = weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1))
  (h29 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 i₀ + weightedSum ω dx (i₀ + 1) ((m : ℤ) - 1) < ε)
  (h30 : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, partitionConditions x dx d δ m → weightedSum ω dx 0 ((m : ℤ) - 1) < ε)
  (h31 : Tendsto (fun (_d : ℝ) => weightedSum ω dx 0 ((n : ℤ) - 1)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  (h32 : riemannOn f 0 1)
  : riemannOn f 0 1 := by
  sorry

end Exercise2194
