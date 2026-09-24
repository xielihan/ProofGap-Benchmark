import Mathlib

/- Differentials at x, evaluated on an arbitrary real increment dx.
The second differential uses a fixed independent increment (d²x = 0).
The source names y itself inside diff; we retain y, not y ∘ u.
See the review for the resulting source statement issue. -/
namespace Exercise1137
noncomputable def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

noncomputable def secondDifferential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv (deriv f) x * dx ^ 2
end Exercise1137

open Exercise1137

/- Exercise 1137, gap 1
SHA-256: 9d888fb476dba3aa25ab35de93b355f439b2aaed6745c78cc5b6f121cbc5ae7b
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. a ∈ RealSet
4. a ∈ PosRealSet
5. DiffableFunc(u)
6. DiffableFunc(FunDeri(u, 1, 1))
7. forall (x), x ∈ RealSet ⇒ y(u(x)) = a^{u(x)}

GOAL:
forall (x), x ∈ RealSet ⇒ diff(y) = a^{u(x)} * ln(a) * diff(u)

METHOD:

-/
theorem proof_gap_exercise_1137_1
  (y u : ℝ → ℝ) (a : ℝ)
  (ha_real : a ∈ (Set.univ : Set ℝ))
  (ha_pos : 0 < a)
  (hu : Differentiable ℝ u)
  (hu' : Differentiable ℝ (deriv u))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y (u x) = Real.rpow a (u x))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ dx : ℝ,
      differential y x dx = Real.rpow a (u x) * Real.log a * differential u x dx := by
  sorry

/- Exercise 1137, gap 2
SHA-256: 89314d71a9accdfee91b9923be9aa141b062100af43cb8f92957354f8fa58c98
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. a ∈ RealSet
4. a ∈ PosRealSet
5. DiffableFunc(u)
6. DiffableFunc(FunDeri(u, 1, 1))
7. forall (x), x ∈ RealSet ⇒ y(u(x)) = a^{u(x)}
8. forall (x), x ∈ RealSet ⇒ diff(y) = a^{u(x)} * ln(a) * diff(u)

GOAL:
forall (x), x ∈ RealSet ⇒ diff^{2}(y) = a^{u(x)} * ln(a)^{2} * diff(u)^{2} + a^{u(x)} * ln(a) * diff^{2}(u)

METHOD:

-/
theorem proof_gap_exercise_1137_2
  (y u : ℝ → ℝ) (a : ℝ)
  (ha_real : a ∈ (Set.univ : Set ℝ))
  (ha_pos : 0 < a)
  (hu : Differentiable ℝ u)
  (hu' : Differentiable ℝ (deriv u))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y (u x) = Real.rpow a (u x))
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ dx : ℝ,
      differential y x dx = Real.rpow a (u x) * Real.log a * differential u x dx)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ dx : ℝ,
      secondDifferential y x dx =
        Real.rpow a (u x) * Real.log a ^ 2 * (differential u x dx) ^ 2 +
        Real.rpow a (u x) * Real.log a * secondDifferential u x dx := by
  sorry

/- Exercise 1137, gap 3
SHA-256: 553405028bc473d0f2d66559595d343404bc7a47c0fe6eaef46905221daf7d99
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. u : RealSet → RealSet
3. a ∈ RealSet
4. a ∈ PosRealSet
5. DiffableFunc(u)
6. DiffableFunc(FunDeri(u, 1, 1))
7. forall (x), x ∈ RealSet ⇒ y(u(x)) = a^{u(x)}
8. forall (x), x ∈ RealSet ⇒ diff(y) = a^{u(x)} * ln(a) * diff(u)
9. forall (x), x ∈ RealSet ⇒ diff^{2}(y) = a^{u(x)} * ln(a)^{2} * diff(u)^{2} + a^{u(x)} * ln(a) * diff^{2}(u)

GOAL:
forall (x), x ∈ RealSet ⇒ diff^{2}(y) = a^{u(x)} * ln(a) * (ln(a) * diff(u)^{2} + diff^{2}(u))

METHOD:

-/
theorem proof_gap_exercise_1137_3
  (y u : ℝ → ℝ) (a : ℝ)
  (ha_real : a ∈ (Set.univ : Set ℝ))
  (ha_pos : 0 < a)
  (hu : Differentiable ℝ u)
  (hu' : Differentiable ℝ (deriv u))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → y (u x) = Real.rpow a (u x))
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ dx : ℝ,
      differential y x dx = Real.rpow a (u x) * Real.log a * differential u x dx)
  (h9 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ dx : ℝ,
      secondDifferential y x dx =
        Real.rpow a (u x) * Real.log a ^ 2 * (differential u x dx) ^ 2 +
        Real.rpow a (u x) * Real.log a * secondDifferential u x dx)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ∀ dx : ℝ,
      secondDifferential y x dx = Real.rpow a (u x) * Real.log a *
        (Real.log a * (differential u x dx) ^ 2 + secondDifferential u x dx) := by
  sorry

