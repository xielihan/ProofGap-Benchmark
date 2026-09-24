import Mathlib

open Filter
open scoped Topology

-- Finite, distinct left and right limits: the standard jump singularity.
def exercise696JumpSingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ l r : ℝ, Tendsto f (𝓝[<] a) (𝓝 l) ∧
    Tendsto f (𝓝[>] a) (𝓝 r) ∧ l ≠ r

-- Exercise 696, gap 1
/-
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = arctan(frac(1, x))

GOAL:
lim_{ x → 0^+ } (y(x)) = frac(π, 2)

METHOD:

-/
theorem proof_gap_exercise_696_1
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = Real.arctan (1 / x))
  : Tendsto y (𝓝[>] 0) (𝓝 (Real.pi / 2)) := by
  sorry

-- Exercise 696, gap 2
/-
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = arctan(frac(1, x))
4. lim_{ x → 0^+ } (y(x)) = frac(π, 2)

GOAL:
lim_{ x → 0^- } (y(x)) = -frac(π, 2)

METHOD:

-/
theorem proof_gap_exercise_696_2
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = Real.arctan (1 / x))
  (hr : Tendsto y (𝓝[>] 0) (𝓝 (Real.pi / 2)))
  : Tendsto y (𝓝[<] 0) (𝓝 (-(Real.pi / 2))) := by
  sorry

-- Exercise 696, gap 3
/-
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = arctan(frac(1, x))
4. lim_{ x → 0^+ } (y(x)) = frac(π, 2)
5. lim_{ x → 0^- } (y(x)) = -frac(π, 2)

GOAL:
JumpSingularPoint(y, 0)

METHOD:

-/
theorem proof_gap_exercise_696_3
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = Real.arctan (1 / x))
  (hr : Tendsto y (𝓝[>] 0) (𝓝 (Real.pi / 2)))
  (hl : Tendsto y (𝓝[<] 0) (𝓝 (-(Real.pi / 2))))
  : exercise696JumpSingularPoint y 0 := by
  sorry

-- Exercise 696, gap 4
/-
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = arctan(frac(1, x))
4. lim_{ x → 0^+ } (y(x)) = frac(π, 2)
5. lim_{ x → 0^- } (y(x)) = -frac(π, 2)
6. JumpSingularPoint(y, 0)

GOAL:
a ∈ { 0 } ⇔ ¬ContinuousFuncAt(y, a)

METHOD:

-/
theorem proof_gap_exercise_696_4
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = Real.arctan (1 / x))
  (hr : Tendsto y (𝓝[>] 0) (𝓝 (Real.pi / 2)))
  (hl : Tendsto y (𝓝[<] 0) (𝓝 (-(Real.pi / 2))))
  (hj : exercise696JumpSingularPoint y 0)
  : a ∈ ({0} : Set ℝ) ↔ ¬ContinuousAt y a := by
  sorry

