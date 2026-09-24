import Mathlib

open scoped BigOperators

namespace Exercise1212

-- The nth differential evaluated on a repeated, arbitrary real increment.
noncomputable def differential (n : ℕ) (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  iteratedFDeriv ℝ n f x (fun _ : Fin n => h)

-- The differential of the restricted coordinate function on the positive half-line.
noncomputable def coordinateDifferential (x h : ℝ) : ℝ :=
  fderivWithin ℝ (fun t : ℝ => t) (Set.Ioi 0) x h

end Exercise1212

open Exercise1212

/- Exercise 1212, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. n ∈ NonNegIntegerSet
3. n ∈ PosIntegerSet
4. forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ y(x) = frac(ln(x), x)

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ diff^{n}(y) = FunDeri(y, 1, n)(x) * diff(fun x [x ∈ RealSet ∧ x ∈ PosRealSet] . x)^{n}

METHOD:

-/
theorem proof_gap_exercise_1212_1
  (y : ℝ → ℝ) (n : ℕ)
  (h_nonneg : n ∈ (Set.univ : Set ℕ))
  (h_pos : 0 < n)
  (h_y : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x → y x = Real.log x / x)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x →
    ∀ h : ℝ, differential n y x h = iteratedDeriv n y x * coordinateDifferential x h ^ n := by
  sorry

/- Exercise 1212, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. n ∈ NonNegIntegerSet
3. n ∈ PosIntegerSet
4. forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ y(x) = frac(ln(x), x)
5. forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ diff^{n}(y) = FunDeri(y, 1, n)(x) * diff(fun x [x ∈ RealSet ∧ x ∈ PosRealSet] . x)^{n}

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ k = 0 }^{ n } (Combination(n, k) * FunDeri(fun x [x ∈ RealSet ∧ x ∈ PosRealSet] . frac(1, x), 1, k)(x) * FunDeri(fun x [x ∈ RealSet ∧ x ∈ PosRealSet] . ln(x), 1, n - k)(x))

METHOD:

-/
theorem proof_gap_exercise_1212_2
  (y : ℝ → ℝ) (n : ℕ)
  (h_nonneg : n ∈ (Set.univ : Set ℕ))
  (h_pos : 0 < n)
  (h_y : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x → y x = Real.log x / x)
  (h_differential : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x →
    ∀ h : ℝ, differential n y x h = iteratedDeriv n y x * coordinateDifferential x h ^ n)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x →
    iteratedDeriv n y x = ∑ k ∈ Finset.Icc 0 n,
      (n.choose k : ℝ) * iteratedDerivWithin k (fun t : ℝ => 1 / t) (Set.Ioi 0) x *
        iteratedDerivWithin (n - k) Real.log (Set.Ioi 0) x := by
  sorry

/- Exercise 1212, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. n ∈ NonNegIntegerSet
3. n ∈ PosIntegerSet
4. forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ y(x) = frac(ln(x), x)
5. forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ diff^{n}(y) = FunDeri(y, 1, n)(x) * diff(fun x [x ∈ RealSet ∧ x ∈ PosRealSet] . x)^{n}
6. forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ FunDeri(y, 1, n)(x) = sum_{ k = 0 }^{ n } (Combination(n, k) * FunDeri(fun x [x ∈ RealSet ∧ x ∈ PosRealSet] . frac(1, x), 1, k)(x) * FunDeri(fun x [x ∈ RealSet ∧ x ∈ PosRealSet] . ln(x), 1, n - k)(x))

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ PosRealSet ⇒ FunDeri(y, 1, n)(x) = frac((-1)^{n} * n!, x^{n + 1}) * (ln(x) - (sum_{ k = 1 }^{ n } (frac(1, k))))

METHOD:

-/
theorem proof_gap_exercise_1212_3
  (y : ℝ → ℝ) (n : ℕ)
  (h_nonneg : n ∈ (Set.univ : Set ℕ))
  (h_pos : 0 < n)
  (h_y : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x → y x = Real.log x / x)
  (h_differential : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x →
    ∀ h : ℝ, differential n y x h = iteratedDeriv n y x * coordinateDifferential x h ^ n)
  (h_leibniz : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x →
    iteratedDeriv n y x = ∑ k ∈ Finset.Icc 0 n,
      (n.choose k : ℝ) * iteratedDerivWithin k (fun t : ℝ => 1 / t) (Set.Ioi 0) x *
        iteratedDerivWithin (n - k) Real.log (Set.Ioi 0) x)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < x →
    iteratedDeriv n y x = ((-1 : ℝ) ^ n * (n.factorial : ℝ) / x ^ (n + 1)) *
      (Real.log x - ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ)) := by
  sorry

