import Mathlib

set_option autoImplicit false

-- Restricted sequence formulas leave the zeroth entries unconstrained.
-- Real and natural-number membership is encoded by binder types.

/- Exercise 789, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))

GOAL:
ContinuousFuncOn(f, IntervalLoRo(0, 1))

METHOD:
-/
theorem proof_gap_exercise_789_1
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  : ContinuousOn f (Set.Ioo (0 : ℝ) 1) := by
  sorry

/- Exercise 789, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))

GOAL:
forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1

METHOD:
-/
theorem proof_gap_exercise_789_2
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1 := by
  sorry

/- Exercise 789, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1

GOAL:
BoundedFuncOn(f, IntervalLoRo(0, 1))

METHOD:
-/
theorem proof_gap_exercise_789_3
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M := by
  sorry

/- Exercise 789, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))

GOAL:
forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)

METHOD:
-/
theorem proof_gap_exercise_789_4
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1 := by
  sorry

/- Exercise 789, gap 5
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))
10. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)

GOAL:
forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ∧ |x(n) - `x'`(n)| = frac(2, n * (n + 1)) ∧ frac(2, n * (n + 1)) < δ))

METHOD:
-/
theorem proof_gap_exercise_789_5
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  (h10 : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1)
  : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |x n - x' n| = 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧ 2 / ((n : ℝ) * ((n : ℝ) + 1)) < δ := by
  sorry

/- Exercise 789, gap 6
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))
10. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)
11. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ∧ |x(n) - `x'`(n)| = frac(2, n * (n + 1)) ∧ frac(2, n * (n + 1)) < δ))

GOAL:
forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ≥ 3 ∧ |f(x(n)) - f(`x'`(n))| = 1))

METHOD:
-/
theorem proof_gap_exercise_789_6
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  (h10 : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1)
  (h11 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |x n - x' n| = 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧ 2 / ((n : ℝ) * ((n : ℝ) + 1)) < δ)
  : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |f (x n) - f (x' n)| = 1 := by
  sorry

/- Exercise 789, gap 7
PROOF GAP @7
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))
10. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)
11. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ∧ |x(n) - `x'`(n)| = frac(2, n * (n + 1)) ∧ frac(2, n * (n + 1)) < δ))
12. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ≥ 3 ∧ |f(x(n)) - f(`x'`(n))| = 1))

GOAL:
forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ 1 > ε_{0})

METHOD:
-/
theorem proof_gap_exercise_789_7
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  (h10 : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1)
  (h11 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |x n - x' n| = 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧ 2 / ((n : ℝ) * ((n : ℝ) + 1)) < δ)
  (h12 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |f (x n) - f (x' n)| = 1)
  : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → 1 > ε₀ := by
  sorry

/- Exercise 789, gap 8
PROOF GAP @8
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))
10. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)
11. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ∧ |x(n) - `x'`(n)| = frac(2, n * (n + 1)) ∧ frac(2, n * (n + 1)) < δ))
12. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ≥ 3 ∧ |f(x(n)) - f(`x'`(n))| = 1))
13. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ 1 > ε_{0})

GOAL:
¬UniformContinuousFuncOn(f, IntervalLoRo(0, 1))

METHOD:
-/
theorem proof_gap_exercise_789_8
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  (h10 : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1)
  (h11 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |x n - x' n| = 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧ 2 / ((n : ℝ) * ((n : ℝ) + 1)) < δ)
  (h12 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |f (x n) - f (x' n)| = 1)
  (h13 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → 1 > ε₀)
  : ¬ UniformContinuousOn f (Set.Ioo (0 : ℝ) 1) := by
  sorry

/- Exercise 789, gap 9
PROOF GAP @9
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))
10. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)
11. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ∧ |x(n) - `x'`(n)| = frac(2, n * (n + 1)) ∧ frac(2, n * (n + 1)) < δ))
12. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ≥ 3 ∧ |f(x(n)) - f(`x'`(n))| = 1))
13. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ 1 > ε_{0})
14. ¬UniformContinuousFuncOn(f, IntervalLoRo(0, 1))

GOAL:
ContinuousFuncOn(f, IntervalLoRo(0, 1))

METHOD:
-/
theorem proof_gap_exercise_789_9
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  (h10 : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1)
  (h11 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |x n - x' n| = 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧ 2 / ((n : ℝ) * ((n : ℝ) + 1)) < δ)
  (h12 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |f (x n) - f (x' n)| = 1)
  (h13 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → 1 > ε₀)
  (h14 : ¬ UniformContinuousOn f (Set.Ioo (0 : ℝ) 1))
  : ContinuousOn f (Set.Ioo (0 : ℝ) 1) := by
  sorry

/- Exercise 789, gap 10
PROOF GAP @10
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))
10. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)
11. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ∧ |x(n) - `x'`(n)| = frac(2, n * (n + 1)) ∧ frac(2, n * (n + 1)) < δ))
12. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ≥ 3 ∧ |f(x(n)) - f(`x'`(n))| = 1))
13. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ 1 > ε_{0})
14. ¬UniformContinuousFuncOn(f, IntervalLoRo(0, 1))
15. ContinuousFuncOn(f, IntervalLoRo(0, 1))

GOAL:
BoundedFuncOn(f, IntervalLoRo(0, 1))

METHOD:
-/
theorem proof_gap_exercise_789_10
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  (h10 : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1)
  (h11 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |x n - x' n| = 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧ 2 / ((n : ℝ) * ((n : ℝ) + 1)) < δ)
  (h12 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |f (x n) - f (x' n)| = 1)
  (h13 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → 1 > ε₀)
  (h14 : ¬ UniformContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h15 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M := by
  sorry

/- Exercise 789, gap 11
PROOF GAP @11
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))
10. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)
11. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ∧ |x(n) - `x'`(n)| = frac(2, n * (n + 1)) ∧ frac(2, n * (n + 1)) < δ))
12. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ≥ 3 ∧ |f(x(n)) - f(`x'`(n))| = 1))
13. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ 1 > ε_{0})
14. ¬UniformContinuousFuncOn(f, IntervalLoRo(0, 1))
15. ContinuousFuncOn(f, IntervalLoRo(0, 1))
16. BoundedFuncOn(f, IntervalLoRo(0, 1))

GOAL:
¬UniformContinuousFuncOn(f, IntervalLoRo(0, 1))

METHOD:
-/
theorem proof_gap_exercise_789_11
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  (h10 : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1)
  (h11 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |x n - x' n| = 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧ 2 / ((n : ℝ) * ((n : ℝ) + 1)) < δ)
  (h12 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |f (x n) - f (x' n)| = 1)
  (h13 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → 1 > ε₀)
  (h14 : ¬ UniformContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h15 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h16 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  : ¬ UniformContinuousOn f (Set.Ioo (0 : ℝ) 1) := by
  sorry

/- Exercise 789, gap 12
PROOF GAP @12
ASSUM:
1. f : RealSet → RealSet
2. x : NonNegIntegerSet → RealSet
3. x' : NonNegIntegerSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ f(t) = sin(frac(π, t))
5. ContinuousFuncOn(f, IntervalLoRo(0, 1))
6. forall (t), t ∈ RealSet ∧ t ∈ IntervalLoRo(0, 1) ⇒ |f(t)| ≤ 1
7. BoundedFuncOn(f, IntervalLoRo(0, 1))
8. x = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n))
9. `x'` = (fun n [n ∈ NonNegIntegerSet ∧ n > 0] . frac(2, n + 1))
10. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ⇒ x(n) ∈ IntervalLoRo(0, 1) ∧ `x'`(n) ∈ IntervalLoRo(0, 1)
11. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ∈ IntegerSet ∧ n ≥ 3 ∧ |x(n) - `x'`(n)| = frac(2, n * (n + 1)) ∧ frac(2, n * (n + 1)) < δ))
12. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (n), n ∈ NonNegIntegerSet ∧ n ≥ 3 ∧ |f(x(n)) - f(`x'`(n))| = 1))
13. forall (ε_{0}), ε_{0} ∈ RealSet ∧ 0 < ε_{0} ∧ ε_{0} < 1 ⇒ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ 1 > ε_{0})
14. ¬UniformContinuousFuncOn(f, IntervalLoRo(0, 1))
15. ContinuousFuncOn(f, IntervalLoRo(0, 1))
16. BoundedFuncOn(f, IntervalLoRo(0, 1))
17. ¬UniformContinuousFuncOn(f, IntervalLoRo(0, 1))

GOAL:
ContinuousFuncOn(f, IntervalLoRo(0, 1)) ∧ BoundedFuncOn(f, IntervalLoRo(0, 1)) ∧ ¬UniformContinuousFuncOn(f, IntervalLoRo(0, 1))

METHOD:
-/
theorem proof_gap_exercise_789_12
  (f : ℝ → ℝ) (x x' : ℕ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → f t = Real.sin (Real.pi / t))
  (h5 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h6 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ 1)
  (h7 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h8 : ∀ n : ℕ, 0 < n → x n = 2 / (n : ℝ))
  (h9 : ∀ n : ℕ, 0 < n → x' n = 2 / ((n : ℝ) + 1))
  (h10 : ∀ n : ℕ, n ≥ 3 → x n ∈ Set.Ioo (0 : ℝ) 1 ∧ x' n ∈ Set.Ioo (0 : ℝ) 1)
  (h11 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |x n - x' n| = 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧ 2 / ((n : ℝ) * ((n : ℝ) + 1)) < δ)
  (h12 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → ∃ n : ℕ, n ≥ 3 ∧ |f (x n) - f (x' n)| = 1)
  (h13 : ∀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 → ∀ δ : ℝ, δ > 0 → 1 > ε₀)
  (h14 : ¬ UniformContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h15 : ContinuousOn f (Set.Ioo (0 : ℝ) 1))
  (h16 : ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M)
  (h17 : ¬ UniformContinuousOn f (Set.Ioo (0 : ℝ) 1))
  : (ContinuousOn f (Set.Ioo (0 : ℝ) 1)) ∧ (∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → |f t| ≤ M) ∧ (¬ UniformContinuousOn f (Set.Ioo (0 : ℝ) 1)) := by
  sorry

