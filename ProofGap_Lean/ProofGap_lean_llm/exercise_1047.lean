import Mathlib

set_option autoImplicit false
set_option linter.style.longLine false

open Filter
open scoped Topology

-- All main proofs intentionally remain sorry, as required.
-- Source error retained: y is actually differentiable at zero (derivative zero).
-- Dom(F) = univ because F : ℝ → ℝ.
-- The piecewise expression is used only off zero; its value at zero is irrelevant.
-- RNFL F'(x(0)) fixes FunDeri(F, x, 1) as deriv F, not a parameter derivative.

/- Exercise 1047, gap 1
PROOF GAP @1
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))

GOAL:
x(0) = 0

METHOD:
-/
theorem proof_gap_exercise_1047_1
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  : x 0 = 0 := by
  sorry

/- Exercise 1047, gap 2
PROOF GAP @2
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0

GOAL:
y(0) = 0

METHOD:
-/
theorem proof_gap_exercise_1047_2
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  : y 0 = 0 := by
  sorry

/- Exercise 1047, gap 3
PROOF GAP @3
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))

GOAL:
forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)

METHOD:
-/
theorem proof_gap_exercise_1047_3
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| := by
  sorry

/- Exercise 1047, gap 4
PROOF GAP @4
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)

GOAL:
forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)

METHOD:
-/
theorem proof_gap_exercise_1047_4
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| := by
  sorry

/- Exercise 1047, gap 5
PROOF GAP @5
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)

GOAL:
forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))

METHOD:
-/
theorem proof_gap_exercise_1047_5
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|) := by
  sorry

/- Exercise 1047, gap 6
PROOF GAP @6
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)
13. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))

GOAL:
forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }))

METHOD:
-/
theorem proof_gap_exercise_1047_6
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  (h13 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|))
  : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (if dt > 0 then 3 * dt else dt) := by
  sorry

/- Exercise 1047, gap 7
PROOF GAP @7
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)
13. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))
14. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }))

GOAL:
lim_{ Δt → 0 } (cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }) = 0

METHOD:
-/
theorem proof_gap_exercise_1047_7
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  (h13 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|))
  (h14 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (if dt > 0 then 3 * dt else dt))
  : Tendsto (fun dt : ℝ => if dt > 0 then 3 * dt else dt) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry

/- Exercise 1047, gap 8
PROOF GAP @8
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)
13. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))
14. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }))
15. lim_{ Δt → 0 } (cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }) = 0

GOAL:
DiffableFuncAt(F, x(0))

METHOD:
-/
theorem proof_gap_exercise_1047_8
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  (h13 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|))
  (h14 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (if dt > 0 then 3 * dt else dt))
  (h15 : Tendsto (fun dt : ℝ => if dt > 0 then 3 * dt else dt) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  : DifferentiableAt ℝ F (x 0) := by
  sorry

/- Exercise 1047, gap 9
PROOF GAP @9
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)
13. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))
14. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }))
15. lim_{ Δt → 0 } (cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }) = 0
16. DiffableFuncAt(F, x(0))

GOAL:
FunDeri(F, x, 1)(x(0)) = 0

METHOD:
-/
theorem proof_gap_exercise_1047_9
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  (h13 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|))
  (h14 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (if dt > 0 then 3 * dt else dt))
  (h15 : Tendsto (fun dt : ℝ => if dt > 0 then 3 * dt else dt) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  (h16 : DifferentiableAt ℝ F (x 0))
  : deriv F (x 0) = 0 := by
  sorry

/- Exercise 1047, gap 10
PROOF GAP @10
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)
13. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))
14. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }))
15. lim_{ Δt → 0 } (cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }) = 0
16. DiffableFuncAt(F, x(0))
17. FunDeri(F, x, 1)(x(0)) = 0

GOAL:
¬DiffableFuncAt(fun t [t ∈ RealSet] . |t|, 0)

METHOD:
-/
theorem proof_gap_exercise_1047_10
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  (h13 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|))
  (h14 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (if dt > 0 then 3 * dt else dt))
  (h15 : Tendsto (fun dt : ℝ => if dt > 0 then 3 * dt else dt) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  (h16 : DifferentiableAt ℝ F (x 0))
  (h17 : deriv F (x 0) = 0)
  : ¬ DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
  sorry

/- Exercise 1047, gap 11
PROOF GAP @11
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)
13. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))
14. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }))
15. lim_{ Δt → 0 } (cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }) = 0
16. DiffableFuncAt(F, x(0))
17. FunDeri(F, x, 1)(x(0)) = 0
18. ¬DiffableFuncAt(fun t [t ∈ RealSet] . |t|, 0)

GOAL:
¬DiffableFuncAt(x, 0)

METHOD:
-/
theorem proof_gap_exercise_1047_11
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  (h13 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|))
  (h14 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (if dt > 0 then 3 * dt else dt))
  (h15 : Tendsto (fun dt : ℝ => if dt > 0 then 3 * dt else dt) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  (h16 : DifferentiableAt ℝ F (x 0))
  (h17 : deriv F (x 0) = 0)
  (h18 : ¬ DifferentiableAt ℝ (fun t : ℝ => |t|) 0)
  : ¬ DifferentiableAt ℝ x 0 := by
  sorry

/- Exercise 1047, gap 12
PROOF GAP @12
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)
13. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))
14. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }))
15. lim_{ Δt → 0 } (cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }) = 0
16. DiffableFuncAt(F, x(0))
17. FunDeri(F, x, 1)(x(0)) = 0
18. ¬DiffableFuncAt(fun t [t ∈ RealSet] . |t|, 0)
19. ¬DiffableFuncAt(x, 0)

GOAL:
¬DiffableFuncAt(y, 0)

METHOD:
-/
theorem proof_gap_exercise_1047_12
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  (h13 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|))
  (h14 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (if dt > 0 then 3 * dt else dt))
  (h15 : Tendsto (fun dt : ℝ => if dt > 0 then 3 * dt else dt) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  (h16 : DifferentiableAt ℝ F (x 0))
  (h17 : deriv F (x 0) = 0)
  (h18 : ¬ DifferentiableAt ℝ (fun t : ℝ => |t|) 0)
  (h19 : ¬ DifferentiableAt ℝ x 0)
  : ¬ DifferentiableAt ℝ y 0 := by
  sorry

/- Exercise 1047, gap 13
PROOF GAP @13
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. forall (t), t ∈ RealSet ⇒ x(t) = 2 * t + |t|
5. forall (t), t ∈ RealSet ⇒ y(t) = 5 * t^{2} + 4 * t * |t|
6. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
7. x(0) = 0
8. y(0) = 0
9. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = x(Δt) - x(0))
10. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = y(Δt) - y(0))
11. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ Δx = 2 * Δt + |Δt|)
12. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δy), Δy ∈ RealSet ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt|)
13. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = frac(5 * Δt^{2} + 4 * Δt * |Δt|, 2 * Δt + |Δt|)))
14. forall (Δt), Δt ∈ RealSet ∧ Δt ≠ 0 ⇒ (exists (Δx), Δx ∈ RealSet ∧ (exists (Δy), Δy ∈ RealSet ∧ Δx = 2 * Δt + |Δt| ∧ Δy = 5 * Δt^{2} + 4 * Δt * |Δt| ∧ frac(Δy, Δx) = cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }))
15. lim_{ Δt → 0 } (cases{ 3 * Δt if Δt > 0; Δt if Δt < 0 }) = 0
16. DiffableFuncAt(F, x(0))
17. FunDeri(F, x, 1)(x(0)) = 0
18. ¬DiffableFuncAt(fun t [t ∈ RealSet] . |t|, 0)
19. ¬DiffableFuncAt(x, 0)
20. ¬DiffableFuncAt(y, 0)

GOAL:
DiffableFuncAt(F, x(0)) ∧ ¬DiffableFuncAt(x, 0) ∧ ¬DiffableFuncAt(y, 0)

METHOD:
-/
theorem proof_gap_exercise_1047_13
  (x y F : ℝ → ℝ)
  (h4 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = 2 * t + |t|)
  (h5 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = 5 * t ^ 2 + 4 * t * |t|)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ (Set.univ : Set ℝ) → y t = F (x t))
  (h7 : x 0 = 0)
  (h8 : y 0 = 0)
  (h9 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = x dt - x 0)
  (h10 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = y dt - y 0)
  (h11 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt|)
  (h12 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt|)
  (h13 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (5 * dt ^ 2 + 4 * dt * |dt|) / (2 * dt + |dt|))
  (h14 : ∀ dt : ℝ, dt ∈ (Set.univ : Set ℝ) ∧ dt ≠ 0 → ∃ dx : ℝ, dx ∈ (Set.univ : Set ℝ) ∧ ∃ dy : ℝ, dy ∈ (Set.univ : Set ℝ) ∧ dx = 2 * dt + |dt| ∧ dy = 5 * dt ^ 2 + 4 * dt * |dt| ∧ dy / dx = (if dt > 0 then 3 * dt else dt))
  (h15 : Tendsto (fun dt : ℝ => if dt > 0 then 3 * dt else dt) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  (h16 : DifferentiableAt ℝ F (x 0))
  (h17 : deriv F (x 0) = 0)
  (h18 : ¬ DifferentiableAt ℝ (fun t : ℝ => |t|) 0)
  (h19 : ¬ DifferentiableAt ℝ x 0)
  (h20 : ¬ DifferentiableAt ℝ y 0)
  : DifferentiableAt ℝ F (x 0) ∧ ¬ DifferentiableAt ℝ x 0 ∧ ¬ DifferentiableAt ℝ y 0 := by
  sorry
