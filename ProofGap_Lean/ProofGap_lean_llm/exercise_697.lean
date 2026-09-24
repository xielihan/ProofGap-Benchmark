import Mathlib

open scoped Topology
open Filter

namespace Exercise697

/-- A removable discontinuity of a total real function: discontinuity and a finite
punctured two-sided limit. The domain closure condition is automatic for ℝ. -/
def RemovableTotal (y : ℝ → ℝ) (a : ℝ) : Prop :=
  ¬ ContinuousAt y a ∧ ∃ L : ℝ, Tendsto y (𝓝[≠] a) (𝓝 L)

/-- For the original positive domain, an omitted boundary point is removable when
it is an accumulation point and the limit along the domain exists and is finite.
At a point belonging to the domain, discontinuity is additionally required. -/
def RemovablePositive (y : {x : ℝ // 0 < x} → ℝ) (a : ℝ) : Prop :=
  (∀ δ : ℝ, 0 < δ → ∃ x : {x : ℝ // 0 < x},
    0 < |(x : ℝ) - a| ∧ |(x : ℝ) - a| < δ) ∧
  (∀ ha : 0 < a, ¬ ContinuousAt y ⟨a, ha⟩) ∧
  ∃ L : ℝ, Tendsto y
    (Filter.comap (fun x : {x : ℝ // 0 < x} => (x : ℝ)) (𝓝[≠] a)) (𝓝 L)

end Exercise697

-- Exercise 697, gap 1
/-
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x > 0 ⇒ y(x) = sqrtn(2, x) * arctan(frac(1, x))

GOAL:
lim_{ x → 0^+ } (y(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_697_1
    (y : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ (Set.univ : Set ℝ))
    (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 →
      y x = Real.sqrt x * Real.arctan (1 / x)) :
    Tendsto y (𝓝[>] 0) (𝓝 0) := by
  sorry

-- Exercise 697, gap 2
/-
PROOF GAP @2
ASSUM:
1. y : PosRealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x > 0 ⇒ y(x) = sqrtn(2, x) * arctan(frac(1, x))
4. lim_{ x → 0^+ } (y(x)) = 0
GOAL:
RemovableSingularPoint(y, 0)

METHOD:

-/
theorem proof_gap_exercise_697_2
    (y : {x : ℝ // 0 < x} → ℝ) (a : ℝ)
    (ha : a ∈ (Set.univ : Set ℝ))
    (hy : ∀ (x : ℝ) (hx : x ∈ (Set.univ : Set ℝ) ∧ x > 0),
      y ⟨x, hx.2⟩ = Real.sqrt x * Real.arctan (1 / x))
    (hlim : Tendsto y
      (Filter.comap (fun x : {x : ℝ // 0 < x} => (x : ℝ)) (𝓝[>] (0 : ℝ)))
      (𝓝 0)) :
    Exercise697.RemovablePositive y 0 := by
  sorry

-- Exercise 697, gap 3
/-
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x > 0 ⇒ y(x) = sqrtn(2, x) * arctan(frac(1, x))
4. lim_{ x → 0^+ } (y(x)) = 0
5. RemovableSingularPoint(y, 0)

GOAL:
a ∈ { 0 } ⇔ ¬ContinuousFuncAt(y, a)

METHOD:

-/
-- The source conclusion is false in general on the declared total domain.
-- See the review for a counterexample; the source statement is retained.
theorem proof_gap_exercise_697_3
    (y : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ (Set.univ : Set ℝ))
    (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x > 0 →
      y x = Real.sqrt x * Real.arctan (1 / x))
    (hlim : Tendsto y (𝓝[>] 0) (𝓝 0))
    (hrem : Exercise697.RemovableTotal y 0) :
    a ∈ ({0} : Set ℝ) ↔ ¬ ContinuousAt y a := by
  sorry

