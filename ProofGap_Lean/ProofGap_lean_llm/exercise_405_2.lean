import Mathlib

open Filter
open scoped Topology

namespace Exercise405_2

-- D is the actual domain; f is an arbitrary total extension of its real values.
-- Values outside D are not specified by restricted function equality.
def Defined (D A : Set ℝ) : Prop := A ⊆ D

def NegativeInfinityAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto f (nhdsWithin a ({a}ᶜ)) atBot

def NegativeBound (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E : ℝ, 0 < E → ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → f x < -E

/- Exercise 405_2, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ Defined(f, IntervalLoRo(a - δ, a) ∪ IntervalLoRo(a, a + δ))

GOAL:
lim_{ x → a } (f(x)) = -∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ f(x) < -E)))

METHOD:

-/
theorem proof_gap_exercise_405_2_1
    (f : ℝ → ℝ) (D : Set ℝ) (a : ℝ)
    (h_defined : ∃ δ : ℝ, 0 < δ ∧
      Defined D (Set.Ioo (a - δ) a ∪ Set.Ioo a (a + δ)))
    : NegativeInfinityAt f a ↔ NegativeBound f a := by
  sorry

/- Exercise 405_2, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ Defined(f, IntervalLoRo(a - δ, a) ∪ IntervalLoRo(a, a + δ))
4. lim_{ x → a } (f(x)) = -∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ f(x) < -E)))
5. f = (fun x [x ∈ RealSet ∧ x ≠ 1] . frac(-1, (x - 1)^{2}))
GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 1 ⇒ f(x) = frac(-1, (x - 1)^{2})

METHOD:

-/
theorem proof_gap_exercise_405_2_2
    (f : ℝ → ℝ) (D : Set ℝ) (a : ℝ)
    (h_defined : ∃ δ : ℝ, 0 < δ ∧
      Defined D (Set.Ioo (a - δ) a ∪ Set.Ioo a (a + δ)))
    (h_characterization : NegativeInfinityAt f a ↔ NegativeBound f a)
    (h_restricted : D = {x : ℝ | x ≠ 1} ∧
      Set.EqOn f (fun x : ℝ => (-1 : ℝ) / (x - 1) ^ (2 : ℕ)) D)
    : ∀ x : ℝ, x ≠ 1 → f x = (-1 : ℝ) / (x - 1) ^ (2 : ℕ) := by
  sorry

/- Exercise 405_2, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ Defined(f, IntervalLoRo(a - δ, a) ∪ IntervalLoRo(a, a + δ))
4. lim_{ x → a } (f(x)) = -∞ ⇔ (forall (E), E ∈ RealSet ∧ E > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |x - a| ∧ |x - a| < δ ⇒ f(x) < -E)))
5. forall (x), x ∈ RealSet ∧ x ≠ 1 ⇒ f(x) = frac(-1, (x - 1)^{2})

GOAL:
lim_{ x → 1 } (f(x)) = -∞

METHOD:

-/
theorem proof_gap_exercise_405_2_3
    (f : ℝ → ℝ) (D : Set ℝ) (a : ℝ)
    (h_defined : ∃ δ : ℝ, 0 < δ ∧
      Defined D (Set.Ioo (a - δ) a ∪ Set.Ioo a (a + δ)))
    (h_characterization : NegativeInfinityAt f a ↔ NegativeBound f a)
    (h_formula : ∀ x : ℝ, x ≠ 1 → f x = (-1 : ℝ) / (x - 1) ^ (2 : ℕ))
    : NegativeInfinityAt f 1 := by
  sorry

end Exercise405_2
