import Mathlib

open Filter
open scoped Topology

-- exercise: exercise_407_3
-- Defined means that each point of the indicated set has a real function value.
-- The source already types f as a total real function; no continuity is asserted.
def exercise4073Defined (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ v : ℝ, f x = v

-- The strict epsilon-delta condition in the source, with real membership
-- discharged by the types of the binders.
def exercise4073Below (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧
    ∀ x : ℝ, 0 < x - a ∧ x - a < δ →
      0 < b - f x ∧ b - f x < ε

-- b - 0 is directional approach from below, not real subtraction.
def exercise4073RightToBelow (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Tendsto f (nhdsWithin a (Set.Ioi a)) (nhdsWithin b (Set.Iio b))

/- Exercise 407_3, gap 1
SHA-256: 820f93378bcd12d3f115238e547a916d53ba8b0e68f268a1b91505128d58fdf4
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, (a, a + `δ_0`))
5. lim_{ x → a } (f(x)) = b
6. forall (x), x ∈ RealSet ∧ x > a ⇒ f(x) < b
GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < b - f(x) ∧ b - f(x) < ε))

METHOD:

-/
theorem proof_gap_exercise_407_3_1
  (f : ℝ → ℝ) (a b : ℝ)
  (h4 : ∃ δ₀ : ℝ, δ₀ > 0 ∧ exercise4073Defined f (Set.Ioo a (a + δ₀)))
  (h5 : Tendsto f (nhdsWithin a ({a}ᶜ : Set ℝ)) (𝓝 b))
  (h6 : ∀ x : ℝ, x > a → f x < b)
  : exercise4073Below f a b := by
  sorry

/- Exercise 407_3, gap 2
SHA-256: 4c2a1a7fac1f7282cb71fb8aa8cd6b5820778d6ddcb951cab8e68595c2713ea7
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, (a, a + `δ_0`))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < b - f(x) ∧ b - f(x) < ε))
6. y = (fun x [x ∈ RealSet] . -x)

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - 0 ∧ x - 0 < δ ⇒ 0 < 0 - y(x) ∧ 0 - y(x) < ε))

METHOD:

-/
theorem proof_gap_exercise_407_3_2
  (f : ℝ → ℝ) (a b : ℝ)
  (h4 : ∃ δ₀ : ℝ, δ₀ > 0 ∧ exercise4073Defined f (Set.Ioo a (a + δ₀)))
  (y : ℝ → ℝ)
  (h5 : exercise4073Below f a b)
  (h6 : y = fun x : ℝ => -x)
  : exercise4073Below y 0 0 := by
  sorry

/- Exercise 407_3, gap 3
SHA-256: 846d0bfe15934ae1b297a73335ebf72fc990773e6689294ff6a3458c52177dbd
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, (a, a + `δ_0`))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < b - f(x) ∧ b - f(x) < ε))
6. y = (fun x [x ∈ RealSet] . -x)
7. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - 0 ∧ x - 0 < δ ⇒ 0 < 0 - y(x) ∧ 0 - y(x) < ε))

GOAL:
lim_{ x → 0^+ } (y(x)) = 0 - 0

METHOD:

-/
theorem proof_gap_exercise_407_3_3
  (f : ℝ → ℝ) (a b : ℝ)
  (h4 : ∃ δ₀ : ℝ, δ₀ > 0 ∧ exercise4073Defined f (Set.Ioo a (a + δ₀)))
  (y : ℝ → ℝ)
  (h5 : exercise4073Below f a b)
  (h6 : y = fun x : ℝ => -x)
  (h7 : exercise4073Below y 0 0)
  : exercise4073RightToBelow y 0 0 := by
  sorry

/- Exercise 407_3, gap 4
SHA-256: 1586ec1e902ff1f8ac9b3238b804c6d7c7b95b69797c21efb34cc1da043e99bf
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. b ∈ RealSet
4. exists (`δ_0`), `δ_0` ∈ RealSet ∧ `δ_0` > 0 ∧ Defined(f, (a, a + `δ_0`))
5. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < b - f(x) ∧ b - f(x) < ε))
6. y = (fun x [x ∈ RealSet] . -x)
7. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - 0 ∧ x - 0 < δ ⇒ 0 < 0 - y(x) ∧ 0 - y(x) < ε))
8. lim_{ x → 0^+ } (y(x)) = 0 - 0

GOAL:
(forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x), x ∈ RealSet ∧ 0 < x - a ∧ x - a < δ ⇒ 0 < b - f(x) ∧ b - f(x) < ε))) ⇔ lim_{ x → a^+ } (f(x)) = b - 0

METHOD:

-/
theorem proof_gap_exercise_407_3_4
  (f : ℝ → ℝ) (a b : ℝ)
  (h4 : ∃ δ₀ : ℝ, δ₀ > 0 ∧ exercise4073Defined f (Set.Ioo a (a + δ₀)))
  (y : ℝ → ℝ)
  (h5 : exercise4073Below f a b)
  (h6 : y = fun x : ℝ => -x)
  (h7 : exercise4073Below y 0 0)
  (h8 : exercise4073RightToBelow y 0 0)
  : exercise4073Below f a b ↔ exercise4073RightToBelow f a b := by
  sorry

