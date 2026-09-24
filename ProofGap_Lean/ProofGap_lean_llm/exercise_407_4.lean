import Mathlib

open Filter
open scoped Topology

namespace Exercise407_4

-- Defined on a set means that every point has a real function value.
-- The source explicitly types f as a total real-to-real function.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ v : ℝ, f x = v

-- The strict epsilon-delta assertion, with all real membership guards retained.
def AboveEstimate (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
    ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < |a - x| ∧ |a - x| < δ →
        0 < f x - b ∧ f x - b < ε

end Exercise407_4

open Exercise407_4

/- Exercise 407_4, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, IntervalLoRo(a - `δ_0`, a) ∪ IntervalLoRo(a, a + `δ_0`))
5. lim_{ x → a } (f(x)) = b
6. forall (x), x ∈ RealSet ∧ x ≠ a ⇒ f(x) > b
GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |a - x| ∧ |a - x| < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))

METHOD:

-/
theorem proof_gap_exercise_407_4_1
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ δ₀ : ℝ, δ₀ ∈ (Set.univ : Set ℝ) ∧ δ₀ > 0 ∧
    DefinedOn f (Set.Ioo (a - δ₀) a ∪ Set.Ioo a (a + δ₀)))
  (h5 : Tendsto f (𝓝[≠] a) (𝓝 b))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ a → f x > b)
  : AboveEstimate f a b := by
  sorry

/- Exercise 407_4, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, IntervalLoRo(a - `δ_0`, a) ∪ IntervalLoRo(a, a + `δ_0`))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |a - x| ∧ |a - x| < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))
6. y = (fun x [x ∈ RealSet] . |x|)

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |0 - x| ∧ |0 - x| < δ ⇒ 0 < y(x) - 0 ∧ y(x) - 0 < ε))

METHOD:

-/
theorem proof_gap_exercise_407_4_2
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ δ₀ : ℝ, δ₀ ∈ (Set.univ : Set ℝ) ∧ δ₀ > 0 ∧
    DefinedOn f (Set.Ioo (a - δ₀) a ∪ Set.Ioo a (a + δ₀)))
  (h5 : AboveEstimate f a b)
  (y : ℝ → ℝ)
  (h6 : y = fun x : ℝ => |x|)
  : AboveEstimate y 0 0 := by
  sorry

/- Exercise 407_4, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, IntervalLoRo(a - `δ_0`, a) ∪ IntervalLoRo(a, a + `δ_0`))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |a - x| ∧ |a - x| < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))
6. y = (fun x [x ∈ RealSet] . |x|)
7. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |0 - x| ∧ |0 - x| < δ ⇒ 0 < y(x) - 0 ∧ y(x) - 0 < ε))

GOAL:
lim_{ x → 0 } (y(x)) = 0 + 0

METHOD:

-/
theorem proof_gap_exercise_407_4_3
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ δ₀ : ℝ, δ₀ ∈ (Set.univ : Set ℝ) ∧ δ₀ > 0 ∧
    DefinedOn f (Set.Ioo (a - δ₀) a ∪ Set.Ioo a (a + δ₀)))
  (h5 : AboveEstimate f a b)
  (y : ℝ → ℝ)
  (h6 : y = fun x : ℝ => |x|)
  (h7 : AboveEstimate y 0 0)
  : Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  sorry

/- Exercise 407_4, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, IntervalLoRo(a - `δ_0`, a) ∪ IntervalLoRo(a, a + `δ_0`))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |a - x| ∧ |a - x| < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))
6. y = (fun x [x ∈ RealSet] . |x|)
7. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |0 - x| ∧ |0 - x| < δ ⇒ 0 < y(x) - 0 ∧ y(x) - 0 < ε))
8. lim_{ x → 0 } (y(x)) = 0 + 0

GOAL:
(forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < |a - x| ∧ |a - x| < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))) ⇔ lim_{ x → a } (f(x)) = b + 0

METHOD:

-/
theorem proof_gap_exercise_407_4_4
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ δ₀ : ℝ, δ₀ ∈ (Set.univ : Set ℝ) ∧ δ₀ > 0 ∧
    DefinedOn f (Set.Ioo (a - δ₀) a ∪ Set.Ioo a (a + δ₀)))
  (h5 : AboveEstimate f a b)
  (y : ℝ → ℝ)
  (h6 : y = fun x : ℝ => |x|)
  (h7 : AboveEstimate y 0 0)
  (h8 : Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
  : AboveEstimate f a b ↔ Tendsto f (𝓝[≠] a) (𝓝[>] b) := by
  sorry

