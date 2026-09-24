import Mathlib

open scoped BigOperators

-- The ordinary higher differential at x, evaluated on a repeated increment dx.
noncomputable def exercise1211Differential (n : ℕ) (y : ℝ → ℝ)
    (x dx : ℝ) : ℝ :=
  iteratedFDeriv ℝ n y x (fun _ : Fin n => dx)

/- Exercise 1211, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. n ∈ NonNegIntegerSet
3. n ∈ PosIntegerSet
4. forall (x), x ∈ RealSet ⇒ y(x) = x^{n} * e^{x}

GOAL:
forall (x), x ∈ RealSet ⇒ diff^{n}(y) = FunDeri(y, 1, n)(x) * diff(fun x [x ∈ RealSet] . x)^{n}

METHOD:

-/
theorem proof_gap_exercise_1211_1
  (y : ℝ → ℝ) (n : ℕ)
  (h_nonneg : n ∈ (Set.univ : Set ℕ))
  (h_pos : 0 < n)
  (h_y : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x ^ n * Real.exp x)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ dx : ℝ, exercise1211Differential n y x dx =
        iteratedDeriv n y x * (fderiv ℝ (fun t : ℝ => t) x dx) ^ n := by
  sorry

/- Exercise 1211, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. n ∈ NonNegIntegerSet
3. n ∈ PosIntegerSet
4. forall (x), x ∈ RealSet ⇒ y(x) = x^{n} * e^{x}
5. forall (x), x ∈ RealSet ⇒ diff^{n}(y) = FunDeri(y, 1, n)(x) * diff(fun x [x ∈ RealSet] . x)^{n}

GOAL:
forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = e^{x} * (sum_{ k = 0 }^{ n } (Combination(n, k) * frac(n!, (n - k)!) * x^{n - k}))

METHOD:

-/
theorem proof_gap_exercise_1211_2
  (y : ℝ → ℝ) (n : ℕ)
  (h_nonneg : n ∈ (Set.univ : Set ℕ))
  (h_pos : 0 < n)
  (h_y : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x ^ n * Real.exp x)
  (h_diff : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ dx : ℝ, exercise1211Differential n y x dx =
        iteratedDeriv n y x * (fderiv ℝ (fun t : ℝ => t) x dx) ^ n)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      iteratedDeriv n y x = Real.exp x *
        (∑ k ∈ Finset.Icc 0 n,
          (n.choose k : ℝ) * ((n.factorial : ℝ) / ((n - k).factorial : ℝ)) *
            x ^ (n - k)) := by
  sorry

/- Exercise 1211, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. n ∈ NonNegIntegerSet
3. n ∈ PosIntegerSet
4. forall (x), x ∈ RealSet ⇒ y(x) = x^{n} * e^{x}
5. forall (x), x ∈ RealSet ⇒ diff^{n}(y) = FunDeri(y, 1, n)(x) * diff(fun x [x ∈ RealSet] . x)^{n}
6. forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = e^{x} * (sum_{ k = 0 }^{ n } (Combination(n, k) * frac(n!, (n - k)!) * x^{n - k}))

GOAL:
forall (x), x ∈ RealSet ⇒ FunDeri(y, 1, n)(x) = e^{x} * (x^{n} + n^{2} * x^{n - 1} + frac(n^{2} * (n - 1)^{2}, 2!) * x^{n - 2} + (sum_{ k = 3 }^{ n } (Combination(n, k) * frac(n!, (n - k)!) * x^{n - k})))

METHOD:

-/
-- Source edge case: n = 1 gives x^(-1); Lean zpow is total also at x = 0.
theorem proof_gap_exercise_1211_3
  (y : ℝ → ℝ) (n : ℕ)
  (h_nonneg : n ∈ (Set.univ : Set ℕ))
  (h_pos : 0 < n)
  (h_y : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y x = x ^ n * Real.exp x)
  (h_diff : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      ∀ dx : ℝ, exercise1211Differential n y x dx =
        iteratedDeriv n y x * (fderiv ℝ (fun t : ℝ => t) x dx) ^ n)
  (h_sum : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      iteratedDeriv n y x = Real.exp x *
        (∑ k ∈ Finset.Icc 0 n,
          (n.choose k : ℝ) * ((n.factorial : ℝ) / ((n - k).factorial : ℝ)) *
            x ^ (n - k)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
      iteratedDeriv n y x = Real.exp x *
        (x ^ n + (n : ℝ) ^ 2 * x ^ ((n : ℤ) - 1) +
          ((n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2 / (Nat.factorial 2 : ℝ)) *
            x ^ ((n : ℤ) - 2) +
          (∑ k ∈ Finset.Icc 3 n,
            (n.choose k : ℝ) * ((n.factorial : ℝ) / ((n - k).factorial : ℝ)) *
              x ^ (n - k))) := by
  sorry

