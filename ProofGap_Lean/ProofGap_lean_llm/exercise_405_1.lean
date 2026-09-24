import Mathlib

open Filter
open scoped Topology

namespace Exercise405_1

-- Unsigned infinite limit, along the punctured domain.
def InfiniteMagnitude (s : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun x => |f x|) (𝓝[s \ {a}] a) atTop

def MagnitudeCondition (s : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E : ℝ, E > 0 → ∃ δ : ℝ, δ > 0 ∧
    ∀ x : ℝ, x ∈ s ∧ 0 < |x - a| ∧ |x - a| < δ → |f x| > E

-- Values outside this subtype domain are used only to express a within-domain limit.
noncomputable def extendAwayOne (f : {x : ℝ // x ≠ 1} → ℝ) : ℝ → ℝ := by
  classical
  exact fun x => if h : x ≠ 1 then f ⟨x, h⟩ else 0

/- Exercise 405_1, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet

GOAL:
lim_{ x → a } (f(x)) = ∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ |f(x)| > E)))

METHOD:

-/
theorem proof_gap_exercise_405_1_1
    (f : ℝ → ℝ) (a : ℝ) :
    InfiniteMagnitude Set.univ f a ↔ MagnitudeCondition Set.univ f a := by
  sorry

/- Exercise 405_1, gap 2
PROOF GAP @2
ASSUM:
1. f = (fun x [x ∈ RealSet ∧ x ≠ 1] . frac(1, x - 1))
2. a ∈ RealSet
3. lim_{ x → a } (f(x)) = ∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ |f(x)| > E)))

GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 1 ⇒ f(x) = frac(1, x - 1)

METHOD:

-/
theorem proof_gap_exercise_405_1_2
    (f : {x : ℝ // x ≠ 1} → ℝ) (a : ℝ)
    (h1 : f = fun x => 1 / (x.val - 1))
    (h3 : InfiniteMagnitude {x | x ≠ 1} (extendAwayOne f) a ↔
      MagnitudeCondition {x | x ≠ 1} (extendAwayOne f) a) :
    ∀ (x : ℝ) (hx : x ≠ 1), f ⟨x, hx⟩ = 1 / (x - 1) := by
  sorry

/- Exercise 405_1, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. lim_{ x → a } (f(x)) = ∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ |f(x)| > E)))
4. forall (x), x ∈ RealSet ∧ x ≠ 1 ⇒ f(x) = frac(1, x - 1)

GOAL:
lim_{ x → 1 } (f(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_405_1_3
    (f : ℝ → ℝ) (a : ℝ)
    (h3 : InfiniteMagnitude Set.univ f a ↔ MagnitudeCondition Set.univ f a)
    (h4 : ∀ x : ℝ, x ≠ 1 → f x = 1 / (x - 1)) :
    InfiniteMagnitude Set.univ f 1 := by
  sorry

end Exercise405_1
