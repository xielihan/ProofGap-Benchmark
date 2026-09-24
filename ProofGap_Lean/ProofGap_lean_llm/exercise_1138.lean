import Mathlib

noncomputable section

namespace Exercise1138

-- Differentials on the common real parameter, evaluated on an arbitrary increment dx.
-- y denotes the dependent composite x ↦ y (u x, v x), as in the source calculation.
def d (f : ℝ → ℝ) (x dx : ℝ) : ℝ := deriv f x * dx

def d2 (f : ℝ → ℝ) (x dx : ℝ) : ℝ := deriv (deriv f) x * dx ^ 2

end Exercise1138

open Exercise1138

/- Exercise 1138, gap 1
PROOF GAP @1
ASSUM:
1. y : CartesianProd(RealSet, RealSet) → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. forall (x), x ∈ RealSet ⇒ u(x) ∈ RealSet
5. forall (x), x ∈ RealSet ⇒ v(x) ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ u(x)^{2} + v(x)^{2} > 0
7. DiffableFunc(u)
8. DiffableFunc(v)
9. DiffableFunc(FunDeri(u, 1, 1))
10. DiffableFunc(FunDeri(v, 1, 1))
11. forall (x), x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0 ⇒ y(u(x), v(x)) = ln(sqrtn(2, u(x)^{2} + v(x)^{2}))

GOAL:
diff(y) = (fun x [x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(u) + (fun x [x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(v)

METHOD:

-/
theorem proof_gap_exercise_1138_1
  (y : ℝ × ℝ → ℝ) (u v : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → v x ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x ^ 2 + v x ^ 2 > 0)
  (h7 : Differentiable ℝ u)
  (h8 : Differentiable ℝ v)
  (h9 : Differentiable ℝ (deriv u))
  (h10 : Differentiable ℝ (deriv v))
  (h11 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    y (u x, v x) = Real.log (Real.sqrt (u x ^ 2 + v x ^ 2)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    ∀ dx : ℝ, d (fun t => y (u t, v t)) x dx =
      (u x / (u x ^ 2 + v x ^ 2)) * d u x dx +
      (v x / (u x ^ 2 + v x ^ 2)) * d v x dx := by
  sorry

/- Exercise 1138, gap 2
PROOF GAP @2
ASSUM:
1. y : CartesianProd(RealSet, RealSet) → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. forall (x), x ∈ RealSet ⇒ u(x) ∈ RealSet
5. forall (x), x ∈ RealSet ⇒ v(x) ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ u(x)^{2} + v(x)^{2} > 0
7. DiffableFunc(u)
8. DiffableFunc(v)
9. DiffableFunc(FunDeri(u, 1, 1))
10. DiffableFunc(FunDeri(v, 1, 1))
11. forall (x), x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0 ⇒ y(u(x), v(x)) = ln(sqrtn(2, u(x)^{2} + v(x)^{2}))
12. diff(y) = (fun x [x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(u) + (fun x [x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(v)

GOAL:
forall (x), x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0 ⇒ diff^{2}(y) = frac((u(x)^{2} + v(x)^{2}) * (diff(u)^{2} + u(x) * diff^{2}(u) + diff(v)^{2} + v(x) * diff^{2}(v)) - 2 * (u(x) * diff(u) + v(x) * diff(v))^{2}, (u(x)^{2} + v(x)^{2})^{2})

METHOD:

-/
theorem proof_gap_exercise_1138_2
  (y : ℝ × ℝ → ℝ) (u v : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → v x ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x ^ 2 + v x ^ 2 > 0)
  (h7 : Differentiable ℝ u)
  (h8 : Differentiable ℝ v)
  (h9 : Differentiable ℝ (deriv u))
  (h10 : Differentiable ℝ (deriv v))
  (h11 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    y (u x, v x) = Real.log (Real.sqrt (u x ^ 2 + v x ^ 2)))
  (h12 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    ∀ dx : ℝ, d (fun t => y (u t, v t)) x dx =
      (u x / (u x ^ 2 + v x ^ 2)) * d u x dx +
      (v x / (u x ^ 2 + v x ^ 2)) * d v x dx)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    ∀ dx : ℝ, d2 (fun t => y (u t, v t)) x dx =
      ((u x ^ 2 + v x ^ 2) *
        ((d u x dx) ^ 2 + u x * d2 u x dx + (d v x dx) ^ 2 + v x * d2 v x dx)
        - 2 * (u x * d u x dx + v x * d v x dx) ^ 2) /
      (u x ^ 2 + v x ^ 2) ^ 2 := by
  sorry

/- Exercise 1138, gap 3
PROOF GAP @3
ASSUM:
1. y : CartesianProd(RealSet, RealSet) → RealSet
2. u : RealSet → RealSet
3. v : RealSet → RealSet
4. forall (x), x ∈ RealSet ⇒ u(x) ∈ RealSet
5. forall (x), x ∈ RealSet ⇒ v(x) ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ u(x)^{2} + v(x)^{2} > 0
7. DiffableFunc(u)
8. DiffableFunc(v)
9. DiffableFunc(FunDeri(u, 1, 1))
10. DiffableFunc(FunDeri(v, 1, 1))
11. forall (x), x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0 ⇒ y(u(x), v(x)) = ln(sqrtn(2, u(x)^{2} + v(x)^{2}))
12. diff(y) = (fun x [x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0] . frac(u(x), u(x)^{2} + v(x)^{2})) * diff(u) + (fun x [x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0] . frac(v(x), u(x)^{2} + v(x)^{2})) * diff(v)
13. forall (x), x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0 ⇒ diff^{2}(y) = frac((u(x)^{2} + v(x)^{2}) * (diff(u)^{2} + u(x) * diff^{2}(u) + diff(v)^{2} + v(x) * diff^{2}(v)) - 2 * (u(x) * diff(u) + v(x) * diff(v))^{2}, (u(x)^{2} + v(x)^{2})^{2})

GOAL:
forall (x), x ∈ RealSet ∧ u(x)^{2} + v(x)^{2} > 0 ⇒ diff^{2}(y) = frac((v(x)^{2} - u(x)^{2}) * diff(u)^{2} - 4 * u(x) * v(x) * diff(u) * diff(v) + (u(x)^{2} - v(x)^{2}) * diff(v)^{2} + (u(x)^{2} + v(x)^{2}) * (u(x) * diff^{2}(u) + v(x) * diff^{2}(v)), (u(x)^{2} + v(x)^{2})^{2})

METHOD:

-/
theorem proof_gap_exercise_1138_3
  (y : ℝ × ℝ → ℝ) (u v : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x ∈ (Set.univ : Set ℝ))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → v x ∈ (Set.univ : Set ℝ))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → u x ^ 2 + v x ^ 2 > 0)
  (h7 : Differentiable ℝ u)
  (h8 : Differentiable ℝ v)
  (h9 : Differentiable ℝ (deriv u))
  (h10 : Differentiable ℝ (deriv v))
  (h11 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    y (u x, v x) = Real.log (Real.sqrt (u x ^ 2 + v x ^ 2)))
  (h12 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    ∀ dx : ℝ, d (fun t => y (u t, v t)) x dx =
      (u x / (u x ^ 2 + v x ^ 2)) * d u x dx +
      (v x / (u x ^ 2 + v x ^ 2)) * d v x dx)
  (h13 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    ∀ dx : ℝ, d2 (fun t => y (u t, v t)) x dx =
      ((u x ^ 2 + v x ^ 2) *
        ((d u x dx) ^ 2 + u x * d2 u x dx + (d v x dx) ^ 2 + v x * d2 v x dx)
        - 2 * (u x * d u x dx + v x * d v x dx) ^ 2) /
      (u x ^ 2 + v x ^ 2) ^ 2)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ u x ^ 2 + v x ^ 2 > 0 →
    ∀ dx : ℝ, d2 (fun t => y (u t, v t)) x dx =
      ((v x ^ 2 - u x ^ 2) * (d u x dx) ^ 2
        - 4 * u x * v x * d u x dx * d v x dx
        + (u x ^ 2 - v x ^ 2) * (d v x dx) ^ 2
        + (u x ^ 2 + v x ^ 2) * (u x * d2 u x dx + v x * d2 v x dx)) /
      (u x ^ 2 + v x ^ 2) ^ 2 := by
  sorry

