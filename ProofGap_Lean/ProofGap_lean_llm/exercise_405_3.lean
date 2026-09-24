import Mathlib

open Filter
open scoped Topology

namespace Exercise405_3

-- Real-valued functions are represented by total real extensions, as in the
-- source type RealSet → RealSet. Values outside a stated domain are unconstrained.
-- Defined retains its assertion that every point of the indicated set has a
-- real value; for the explicitly total source type this is automatic.
def Defined (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  Set.MapsTo f s Set.univ

-- Positive infinity is a filter limit, not a real-valued limit equal to a number.
def PositiveInfinityAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto f (𝓝[≠] a) atTop

def PositiveThresholdCondition (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E : ℝ, E ∈ (Set.univ : Set ℝ) ∧ E > 0 →
    ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < |x - a| ∧ |x - a| < δ →
        f x > E

end Exercise405_3

open Exercise405_3

/- Exercise 405_3, gap 1
SHA-256: b84a28eb96b3baa58f6d54825d47ae6a46a1a4b38bbf9d560d3a48c7320f25a4
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ Defined(f, IntervalLoRo(a - δ, a) ∪ IntervalLoRo(a, a + δ))

GOAL:
lim_{ x → a } (f(x)) = +∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ f(x) > E)))

METHOD:

-/
theorem proof_gap_exercise_405_3_1
  (f : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hdefined : ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
    Defined f (Set.Ioo (a - δ) a ∪ Set.Ioo a (a + δ)))
  : PositiveInfinityAt f a ↔ PositiveThresholdCondition f a := by
  sorry

/- Exercise 405_3, gap 2
SHA-256: 89eff07ac18b294b94d97086df38d9b6954eb46ac0be6a5fac4680255eac4c27
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ Defined(f, IntervalLoRo(a - δ, a) ∪ IntervalLoRo(a, a + δ))
4. lim_{ x → a } (f(x)) = +∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ f(x) > E)))
5. f = (fun x [x ∈ RealSet ∧ x ≠ 1] . frac(1, (x - 1)^{2}))
GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 1 ⇒ f(x) = frac(1, (x - 1)^{2})

METHOD:

-/
theorem proof_gap_exercise_405_3_2
  (f : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hdefined : ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
    Defined f (Set.Ioo (a - δ) a ∪ Set.Ioo a (a + δ)))
  (hcriterion : PositiveInfinityAt f a ↔ PositiveThresholdCondition f a)
  (hformula : (fun x : {x : ℝ // x ≠ 1} => f x.val) =
    (fun x : {x : ℝ // x ≠ 1} => (1 : ℝ) / (x.val - 1) ^ (2 : ℕ)))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 →
    f x = (1 : ℝ) / (x - 1) ^ (2 : ℕ) := by
  sorry

/- Exercise 405_3, gap 3
SHA-256: 73688d1d9954c30d73b5ba03ab588871cfc9e685e825b943fb3fad0f5d180b4e
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ Defined(f, IntervalLoRo(a - δ, a) ∪ IntervalLoRo(a, a + δ))
4. lim_{ x → a } (f(x)) = +∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ f(x) > E)))
5. forall (x), x ∈ RealSet ∧ x ≠ 1 ⇒ f(x) = frac(1, (x - 1)^{2})

GOAL:
lim_{ x → 1 } (f(x)) = +∞

METHOD:

-/
theorem proof_gap_exercise_405_3_3
  (f : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hdefined : ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
    Defined f (Set.Ioo (a - δ) a ∪ Set.Ioo a (a + δ)))
  (hcriterion : PositiveInfinityAt f a ↔ PositiveThresholdCondition f a)
  (hformula : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 →
    f x = (1 : ℝ) / (x - 1) ^ (2 : ℕ))
  : PositiveInfinityAt f 1 := by
  sorry

