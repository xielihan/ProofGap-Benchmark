import Mathlib

open Filter
open scoped Topology

namespace Exercise407_5

-- A total real function is defined on s when each input in s has a real value.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ z : ℝ, f x = z

-- The strict inequalities specifying approach from the left and from above.
def LeftAboveEstimate (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
    ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 < a - x ∧ a - x < δ →
        0 < f x - b ∧ f x - b < ε

/- Exercise 407_5, gap 1
SHA-256: 44986fc293c0d1b7616b4d0ce13f972c3f10e4c1a0d5511bdb98ea5ec90e7d10
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, (a - `δ_0`, a))
5. lim_{ x → a } (f(x)) = b
6. forall (x), x ∈ RealSet ∧ x < a ⇒ f(x) > b
GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))

METHOD:

-/
theorem proof_gap_exercise_407_5_1
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ δ₀ : ℝ, δ₀ ∈ (Set.univ : Set ℝ) ∧ δ₀ > 0 ∧
    DefinedOn f (Set.Ioo (a - δ₀) a))
  (h5 : Tendsto f (𝓝[≠] a) (𝓝 b))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x < a → f x > b)
  : LeftAboveEstimate f a b := by
  sorry

/- Exercise 407_5, gap 2
SHA-256: b6be13097617d762bfb6188ee589059c2ae2a7351d144d1ec35b525a43da8e0f
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, (a - `δ_0`, a))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))
6. y = (fun x [x ∈ RealSet] . -x)

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < 0 - x ∧ 0 - x < δ ⇒ 0 < y(x) - 0 ∧ y(x) - 0 < ε))

METHOD:

-/
theorem proof_gap_exercise_407_5_2
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ δ₀ : ℝ, δ₀ ∈ (Set.univ : Set ℝ) ∧ δ₀ > 0 ∧
    DefinedOn f (Set.Ioo (a - δ₀) a))
  (h5 : LeftAboveEstimate f a b)
  (y : ℝ → ℝ)
  (h6 : y = fun x : ℝ => -x)
  : LeftAboveEstimate y 0 0 := by
  sorry

/- Exercise 407_5, gap 3
SHA-256: 74996af1db8a3768e25e5b12c74acc32a526691b4ec6380409dd40d8013b3181
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, (a - `δ_0`, a))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))
6. y = (fun x [x ∈ RealSet] . -x)
7. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < 0 - x ∧ 0 - x < δ ⇒ 0 < y(x) - 0 ∧ y(x) - 0 < ε))

GOAL:
lim_{ x → 0^- } (y(x)) = 0 + 0

METHOD:

-/
theorem proof_gap_exercise_407_5_3
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ δ₀ : ℝ, δ₀ ∈ (Set.univ : Set ℝ) ∧ δ₀ > 0 ∧
    DefinedOn f (Set.Ioo (a - δ₀) a))
  (h5 : LeftAboveEstimate f a b)
  (y : ℝ → ℝ)
  (h6 : y = fun x : ℝ => -x)
  (h7 : LeftAboveEstimate y 0 0)
  : Tendsto y (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  sorry

/- Exercise 407_5, gap 4
SHA-256: 1551431159ce04afeeb84cf92cb88e36e971d1def7a5d51a53dbeeca267103d8
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, (a - `δ_0`, a))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))
6. y = (fun x [x ∈ RealSet] . -x)
7. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < 0 - x ∧ 0 - x < δ ⇒ 0 < y(x) - 0 ∧ y(x) - 0 < ε))
8. lim_{ x → 0^- } (y(x)) = 0 + 0

GOAL:
(forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < a - x ∧ a - x < δ ⇒ 0 < f(x) - b ∧ f(x) - b < ε))) ⇔ lim_{ x → a^- } (f(x)) = b + 0

METHOD:

-/
theorem proof_gap_exercise_407_5_4
  (f : ℝ → ℝ) (a b : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : ∃ δ₀ : ℝ, δ₀ ∈ (Set.univ : Set ℝ) ∧ δ₀ > 0 ∧
    DefinedOn f (Set.Ioo (a - δ₀) a))
  (h5 : LeftAboveEstimate f a b)
  (y : ℝ → ℝ)
  (h6 : y = fun x : ℝ => -x)
  (h7 : LeftAboveEstimate y 0 0)
  (h8 : Tendsto y (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
  : LeftAboveEstimate f a b ↔ Tendsto f (𝓝[<] a) (𝓝[>] b) := by
  sorry

end Exercise407_5
