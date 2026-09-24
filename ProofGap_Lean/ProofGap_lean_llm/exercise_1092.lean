import Mathlib

/- Exercise 1092, gap 1
PROOF GAP @1
ASSUM:
1. u : RealSet → RealSet
2. v : RealSet → RealSet
3. y : RealSet → RealSet
4. DiffableFunc(u)
5. DiffableFunc(v)
6. forall (x), x ∈ RealSet ∧ v(x) ≠ 0 ⇒ y(x) = frac(u(x), v(x)^{2})

GOAL:
forall (x), x ∈ RealSet ∧ v(x) ≠ 0 ⇒ diff(y) = (fun x [x ∈ RealSet ∧ v(x) ≠ 0] . frac(v(x)^{2}, v(x)^{4})) * diff(u) - (fun x [x ∈ RealSet ∧ v(x) ≠ 0] . frac(2 * u(x) * v(x), v(x)^{4})) * diff(v) ∧ (fun x [x ∈ RealSet ∧ v(x) ≠ 0] . frac(v(x)^{2}, v(x)^{4})) * diff(u) - (fun x [x ∈ RealSet ∧ v(x) ≠ 0] . frac(2 * u(x) * v(x), v(x)^{4})) * diff(v) = (fun x [x ∈ RealSet ∧ v(x) ≠ 0] . frac(v(x), v(x)^{3})) * diff(u) - (fun x [x ∈ RealSet ∧ v(x) ≠ 0] . frac(2 * u(x), v(x)^{3})) * diff(v)

METHOD:

-/

namespace Exercise1092

-- The common domain of all restricted coefficient and differential fields.
abbrev Domain (v : ℝ → ℝ) := {x : ℝ // x ∈ (Set.univ : Set ℝ) ∧ v x ≠ 0}

-- Ambient real differential, restricted in its base point to the stated domain.
noncomputable def differential (v f : ℝ → ℝ) : Domain v → (ℝ →L[ℝ] ℝ) :=
  fun p => fderiv ℝ f p.val

end Exercise1092

open Exercise1092 in
 theorem proof_gap_exercise_1092_1
    (u v y : ℝ → ℝ)
    (h1 : Differentiable ℝ u)
    (h2 : Differentiable ℝ v)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ v x ≠ 0 →
      y x = u x / (v x) ^ 2) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ v x ≠ 0 →
      (differential v y =
        (fun p : Domain v => (v p.val) ^ 2 / (v p.val) ^ 4) • differential v u -
        (fun p : Domain v => 2 * u p.val * v p.val / (v p.val) ^ 4) • differential v v) ∧
      ((fun p : Domain v => (v p.val) ^ 2 / (v p.val) ^ 4) • differential v u -
        (fun p : Domain v => 2 * u p.val * v p.val / (v p.val) ^ 4) • differential v v =
       (fun p : Domain v => v p.val / (v p.val) ^ 3) • differential v u -
        (fun p : Domain v => 2 * u p.val / (v p.val) ^ 3) • differential v v) := by
  sorry
