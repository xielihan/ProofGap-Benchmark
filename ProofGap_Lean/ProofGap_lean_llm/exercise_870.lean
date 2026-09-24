import Mathlib

/- Exercise 870, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ cos(x) + x * sin(x) ≠ 0 ⇒ y(x) = frac(sin(x) - x * cos(x), cos(x) + x * sin(x))

GOAL:
forall (x), x ∈ RealSet ∧ cos(x) + x * sin(x) ≠ 0 ⇒ FunDeri(y, x, 1)(x) = frac((x * sin(x) - cos(x) + cos(x)) * (cos(x) + x * sin(x)) - (sin(x) - sin(x) + x * cos(x)) * (sin(x) - x * cos(x)), (cos(x) + x * sin(x))^{2})

METHOD:

-/
theorem proof_gap_exercise_870_1
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.cos x + x * Real.sin x ≠ 0 →
    y x = (Real.sin x - x * Real.cos x) / (Real.cos x + x * Real.sin x))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.cos x + x * Real.sin x ≠ 0 →
    iteratedDeriv 1 y x =
      ((x * Real.sin x - Real.cos x + Real.cos x) * (Real.cos x + x * Real.sin x) -
        (Real.sin x - Real.sin x + x * Real.cos x) * (Real.sin x - x * Real.cos x)) /
      (Real.cos x + x * Real.sin x) ^ 2 := by
  sorry

/- Exercise 870, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ cos(x) + x * sin(x) ≠ 0 ⇒ y(x) = frac(sin(x) - x * cos(x), cos(x) + x * sin(x))
3. forall (x), x ∈ RealSet ∧ cos(x) + x * sin(x) ≠ 0 ⇒ FunDeri(y, x, 1)(x) = frac((x * sin(x) - cos(x) + cos(x)) * (cos(x) + x * sin(x)) - (sin(x) - sin(x) + x * cos(x)) * (sin(x) - x * cos(x)), (cos(x) + x * sin(x))^{2})

GOAL:
forall (x), x ∈ RealSet ∧ cos(x) + x * sin(x) ≠ 0 ⇒ FunDeri(y, x, 1)(x) = frac(x^{2}, (cos(x) + x * sin(x))^{2})

METHOD:

-/
theorem proof_gap_exercise_870_2
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.cos x + x * Real.sin x ≠ 0 →
    y x = (Real.sin x - x * Real.cos x) / (Real.cos x + x * Real.sin x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.cos x + x * Real.sin x ≠ 0 →
    iteratedDeriv 1 y x =
      ((x * Real.sin x - Real.cos x + Real.cos x) * (Real.cos x + x * Real.sin x) -
        (Real.sin x - Real.sin x + x * Real.cos x) * (Real.sin x - x * Real.cos x)) /
      (Real.cos x + x * Real.sin x) ^ 2)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ Real.cos x + x * Real.sin x ≠ 0 →
    iteratedDeriv 1 y x = x ^ 2 / (Real.cos x + x * Real.sin x) ^ 2 := by
  sorry

