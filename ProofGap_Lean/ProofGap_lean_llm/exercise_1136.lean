import Mathlib

-- Differentials along the common real parameter x, evaluated on an arbitrary dx.
-- In particular, diff(y) means the differential of x ↦ y (u x, v x).
noncomputable def exercise1136_d1 (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

noncomputable def exercise1136_d2 (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv (deriv f) x * dx ^ 2

/- Exercise 1136, gap 1
SHA-256: 048d91aff6b9d31d2ee2b44ba83b1c2676053627fa7d9440447773665b6cdea9
PROOF GAP @1
ASSUM:
1. y : CartesianProd(RealSet, RealSet) → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. m ∈ RealSet
5. n ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ u(x) > 0
7. forall (x), x ∈ RealSet ⇒ v(x) > 0
8. DiffableFunc(u)
9. DiffableFunc(v)
10. DiffableFunc(FunDeri(u, 1, 1))
11. DiffableFunc(FunDeri(v, 1, 1))
12. forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ y(u(x), v(x)) = u(x)^{m} * v(x)^{n}

GOAL:
forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ diff(y) = m * u(x)^{m - 1} * v(x)^{n} * diff(u) + n * u(x)^{m} * v(x)^{n - 1} * diff(v)

METHOD:

-/
theorem proof_gap_exercise_1136_1
  (y : ℝ × ℝ → ℝ) (u v : ℝ → ℝ) (m n : ℝ)
  (h4 : m ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x > 0)
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → v x > 0)
  (h8 : Differentiable ℝ u)
  (h9 : Differentiable ℝ v)
  (h10 : Differentiable ℝ (deriv u))
  (h11 : Differentiable ℝ (deriv v))
  (h12 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 →
    y (u x, v x) = Real.rpow (u x) m * Real.rpow (v x) n)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 → ∀ dx : ℝ,
    exercise1136_d1 (fun t => y (u t, v t)) x dx =
      m * Real.rpow (u x) (m - 1) * Real.rpow (v x) n * exercise1136_d1 u x dx +
      n * Real.rpow (u x) m * Real.rpow (v x) (n - 1) * exercise1136_d1 v x dx := by
  sorry

/- Exercise 1136, gap 2
SHA-256: c6774e411d3f3bbbb2faf0e72e073cfaf40dda23000bcaaeda1eeeabae06b0de
PROOF GAP @2
ASSUM:
1. y : CartesianProd(RealSet, RealSet) → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. m ∈ RealSet
5. n ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ u(x) > 0
7. forall (x), x ∈ RealSet ⇒ v(x) > 0
8. DiffableFunc(u)
9. DiffableFunc(v)
10. DiffableFunc(FunDeri(u, 1, 1))
11. DiffableFunc(FunDeri(v, 1, 1))
12. forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ y(u(x), v(x)) = u(x)^{m} * v(x)^{n}
13. forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ diff(y) = m * u(x)^{m - 1} * v(x)^{n} * diff(u) + n * u(x)^{m} * v(x)^{n - 1} * diff(v)

GOAL:
forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ diff^{2}(y) = m * (m - 1) * u(x)^{m - 2} * v(x)^{n} * diff(u)^{2} + m * u(x)^{m - 1} * (v(x)^{n} * diff^{2}(u) + n * v(x)^{n - 1} * diff(u) * diff(v)) + m * n * u(x)^{m - 1} * v(x)^{n - 1} * diff(u) * diff(v) + n * (n - 1) * u(x)^{m} * v(x)^{n - 2} * diff(v)^{2} + n * u(x)^{m} * v(x)^{n - 1} * diff^{2}(v)

METHOD:

-/
theorem proof_gap_exercise_1136_2
  (y : ℝ × ℝ → ℝ) (u v : ℝ → ℝ) (m n : ℝ)
  (h4 : m ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x > 0)
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → v x > 0)
  (h8 : Differentiable ℝ u)
  (h9 : Differentiable ℝ v)
  (h10 : Differentiable ℝ (deriv u))
  (h11 : Differentiable ℝ (deriv v))
  (h12 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 →
    y (u x, v x) = Real.rpow (u x) m * Real.rpow (v x) n)
  (h13 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 → ∀ dx : ℝ,
    exercise1136_d1 (fun t => y (u t, v t)) x dx =
      m * Real.rpow (u x) (m - 1) * Real.rpow (v x) n * exercise1136_d1 u x dx +
      n * Real.rpow (u x) m * Real.rpow (v x) (n - 1) * exercise1136_d1 v x dx)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 → ∀ dx : ℝ,
    exercise1136_d2 (fun t => y (u t, v t)) x dx =
      m * (m - 1) * Real.rpow (u x) (m - 2) * Real.rpow (v x) n * (exercise1136_d1 u x dx) ^ 2 +
      m * Real.rpow (u x) (m - 1) *
        (Real.rpow (v x) n * exercise1136_d2 u x dx +
         n * Real.rpow (v x) (n - 1) * exercise1136_d1 u x dx * exercise1136_d1 v x dx) +
      m * n * Real.rpow (u x) (m - 1) * Real.rpow (v x) (n - 1) *
        exercise1136_d1 u x dx * exercise1136_d1 v x dx +
      n * (n - 1) * Real.rpow (u x) m * Real.rpow (v x) (n - 2) * (exercise1136_d1 v x dx) ^ 2 +
      n * Real.rpow (u x) m * Real.rpow (v x) (n - 1) * exercise1136_d2 v x dx := by
  sorry

/- Exercise 1136, gap 3
SHA-256: 38e27e6c976eaeb19ccb86466920f55b20bd2d9029f74efb1b302d24fceaf9b2
PROOF GAP @3
ASSUM:
1. y : CartesianProd(RealSet, RealSet) → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. m ∈ RealSet
5. n ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ u(x) > 0
7. forall (x), x ∈ RealSet ⇒ v(x) > 0
8. DiffableFunc(u)
9. DiffableFunc(v)
10. DiffableFunc(FunDeri(u, 1, 1))
11. DiffableFunc(FunDeri(v, 1, 1))
12. forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ y(u(x), v(x)) = u(x)^{m} * v(x)^{n}
13. forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ diff(y) = m * u(x)^{m - 1} * v(x)^{n} * diff(u) + n * u(x)^{m} * v(x)^{n - 1} * diff(v)
14. forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ diff^{2}(y) = m * (m - 1) * u(x)^{m - 2} * v(x)^{n} * diff(u)^{2} + m * u(x)^{m - 1} * (v(x)^{n} * diff^{2}(u) + n * v(x)^{n - 1} * diff(u) * diff(v)) + m * n * u(x)^{m - 1} * v(x)^{n - 1} * diff(u) * diff(v) + n * (n - 1) * u(x)^{m} * v(x)^{n - 2} * diff(v)^{2} + n * u(x)^{m} * v(x)^{n - 1} * diff^{2}(v)

GOAL:
forall (x), x ∈ RealSet ∧ u(x) > 0 ∧ v(x) > 0 ⇒ diff^{2}(y) = u(x)^{m - 2} * v(x)^{n - 2} * (m * (m - 1) * v(x)^{2} * diff(u)^{2} + 2 * m * n * u(x) * v(x) * diff(u) * diff(v) + n * (n - 1) * u(x)^{2} * diff(v)^{2} + u(x) * v(x) * (m * v(x) * diff^{2}(u) + n * u(x) * diff^{2}(v)))

METHOD:

-/
theorem proof_gap_exercise_1136_3
  (y : ℝ × ℝ → ℝ) (u v : ℝ → ℝ) (m n : ℝ)
  (h4 : m ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x > 0)
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → v x > 0)
  (h8 : Differentiable ℝ u)
  (h9 : Differentiable ℝ v)
  (h10 : Differentiable ℝ (deriv u))
  (h11 : Differentiable ℝ (deriv v))
  (h12 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 →
    y (u x, v x) = Real.rpow (u x) m * Real.rpow (v x) n)
  (h13 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 → ∀ dx : ℝ,
    exercise1136_d1 (fun t => y (u t, v t)) x dx =
      m * Real.rpow (u x) (m - 1) * Real.rpow (v x) n * exercise1136_d1 u x dx +
      n * Real.rpow (u x) m * Real.rpow (v x) (n - 1) * exercise1136_d1 v x dx)
  (h14 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 → ∀ dx : ℝ,
    exercise1136_d2 (fun t => y (u t, v t)) x dx =
      m * (m - 1) * Real.rpow (u x) (m - 2) * Real.rpow (v x) n * (exercise1136_d1 u x dx) ^ 2 +
      m * Real.rpow (u x) (m - 1) *
        (Real.rpow (v x) n * exercise1136_d2 u x dx +
         n * Real.rpow (v x) (n - 1) * exercise1136_d1 u x dx * exercise1136_d1 v x dx) +
      m * n * Real.rpow (u x) (m - 1) * Real.rpow (v x) (n - 1) *
        exercise1136_d1 u x dx * exercise1136_d1 v x dx +
      n * (n - 1) * Real.rpow (u x) m * Real.rpow (v x) (n - 2) * (exercise1136_d1 v x dx) ^ 2 +
      n * Real.rpow (u x) m * Real.rpow (v x) (n - 1) * exercise1136_d2 v x dx)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x > 0 ∧ v x > 0 → ∀ dx : ℝ,
    exercise1136_d2 (fun t => y (u t, v t)) x dx =
      Real.rpow (u x) (m - 2) * Real.rpow (v x) (n - 2) *
        (m * (m - 1) * (v x) ^ 2 * (exercise1136_d1 u x dx) ^ 2 +
         2 * m * n * u x * v x * exercise1136_d1 u x dx * exercise1136_d1 v x dx +
         n * (n - 1) * (u x) ^ 2 * (exercise1136_d1 v x dx) ^ 2 +
         u x * v x * (m * v x * exercise1136_d2 u x dx + n * u x * exercise1136_d2 v x dx)) := by
  sorry

