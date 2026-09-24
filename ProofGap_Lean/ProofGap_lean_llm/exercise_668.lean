import Mathlib

-- Domain of the graph of the given total real function (Thm 220).
def exercise668Dom (f : ℝ → ℝ) : Set ℝ :=
  {x | ∃ y : ℝ, f x = y}

/- Exercise 668, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. x_{0} ∈ RealSet
3. ε_{0} ∈ RealSet
4. x_{0} ∈ Dom(f)
5. ¬ContinuousFuncAt(f, x_{0})
GOAL:
exists (ε_{0}), ε_{0} ∈ RealSet ∧ ε_{0} > 0 ∧ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x - x_{0}| < δ ∧ |f(x) - f(x_{0})| ≥ ε_{0}))

METHOD:

-/
theorem proof_gap_exercise_668_1
    (f : ℝ → ℝ) (x₀ ε₀ : ℝ)
    (hx₀ : x₀ ∈ (Set.univ : Set ℝ))
    (hε₀ : ε₀ ∈ (Set.univ : Set ℝ))
    (hdom : x₀ ∈ exercise668Dom f)
    (hdiscontinuous : ¬ ContinuousAt f x₀) :
    ∃ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧
      (∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
        ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ exercise668Dom f ∧
          |x - x₀| < δ ∧ |f x - f x₀| ≥ ε) := by
  sorry

/- Exercise 668, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. x_{0} ∈ RealSet
3. ε_{0} ∈ RealSet
4. x_{0} ∈ Dom(f)
5. exists (ε_{0}), ε_{0} ∈ RealSet ∧ ε_{0} > 0 ∧ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x - x_{0}| < δ ∧ |f(x) - f(x_{0})| ≥ ε_{0}))

GOAL:
(exists (ε_{0}), ε_{0} ∈ RealSet ∧ ε_{0} > 0 ∧ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x - x_{0}| < δ ∧ |f(x) - f(x_{0})| ≥ ε_{0}))) ⇒ ε_{0} > 0 ∧ (forall (δ), δ ∈ RealSet ∧ δ > 0 ⇒ (exists (x), x ∈ RealSet ∧ x ∈ Dom(f) ∧ |x - x_{0}| < δ ∧ |f(x) - f(x_{0})| ≥ ε_{0}))

METHOD:

-/
-- The existential ε does not bind the outer ε₀ in the conclusion.
-- This source statement is false; its exact direction and scope are preserved.
theorem proof_gap_exercise_668_2
    (f : ℝ → ℝ) (x₀ ε₀ : ℝ)
    (hx₀ : x₀ ∈ (Set.univ : Set ℝ))
    (hε₀ : ε₀ ∈ (Set.univ : Set ℝ))
    (hdom : x₀ ∈ exercise668Dom f)
    (hex : ∃ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧
      (∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
        ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ exercise668Dom f ∧
          |x - x₀| < δ ∧ |f x - f x₀| ≥ ε)) :
    (∃ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧
      (∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
        ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ exercise668Dom f ∧
          |x - x₀| < δ ∧ |f x - f x₀| ≥ ε)) →
    ε₀ > 0 ∧
      (∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
        ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ exercise668Dom f ∧
          |x - x₀| < δ ∧ |f x - f x₀| ≥ ε₀) := by
  sorry
