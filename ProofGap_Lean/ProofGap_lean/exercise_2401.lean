import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

open scoped RealInnerProductSpace

noncomputable def lpFunDeri {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f g : E -> ℝ) : E -> ℝ :=
  fun x => (inner ℝ (gradient f x) (gradient g x)) /. (‖gradient g x‖ ^ 2)

def lpLeftDifferentiable (f : ℝ -> ℝ) : Prop :=
  ∀ x, DifferentiableWithinAt ℝ f (Set.Iio x) x

def lpRightDifferentiable (f : ℝ -> ℝ) : Prop :=
  ∀ x, DifferentiableWithinAt ℝ f (Set.Ioi x) x

def lpLeftDifferentiableOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ f (s ∩ Set.Iio x) x

def lpRightDifferentiableOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ f (s ∩ Set.Ioi x) x

def lpMaximumPoints {α β : Type*} [Preorder β] (f : α -> β) : Set α :=
  {x | ∀ y, f y ≤ f x}

def lpMinimumPoints {α β : Type*} [Preorder β] (f : α -> β) : Set α :=
  {x | ∀ y, f x ≤ f y}

def lpMaximumPointsOn {α β : Type*} [Preorder β] (f : α -> β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f y ≤ f x}

def lpMinimumPointsOn {α β : Type*} [Preorder β] (f : α -> β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f x ≤ f y}

noncomputable def lpRadiusOfConvergence {𝕜 : Type*} [NormedField 𝕜] (a : ℕ -> 𝕜) : ENNReal :=
  ⨆ (r : NNReal), ⨆ (_h : Summable (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n)), (r : ENNReal)

-- exercise: exercise_2401

theorem proof_gap_exercise_2401_1
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  : S = (∫ x in (0 : ℝ)..Real.pi, (((x + ((Real.sin x) ^ (2 : ℕ))) - x) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2401_2
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : S = (∫ x in (0 : ℝ)..Real.pi, (((x + ((Real.sin x) ^ (2 : ℕ))) - x) * (1 : ℝ))))
  : S = (((Real.pi /. 2) - ((1 /. 4) * (Real.sin (2 * Real.pi)))) - ((0 /. 2) - ((1 /. 4) * (Real.sin (2 * 0))))) := by
  sorry

theorem proof_gap_exercise_2401_3
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : S = (∫ x in (0 : ℝ)..Real.pi, (((x + ((Real.sin x) ^ (2 : ℕ))) - x) * (1 : ℝ))))
  (h3 : S = (((Real.pi /. 2) - ((1 /. 4) * (Real.sin (2 * Real.pi)))) - ((0 /. 2) - ((1 /. 4) * (Real.sin (2 * 0))))))
  : S = (Real.pi /. 2) := by
  sorry
