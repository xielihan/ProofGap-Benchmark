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

-- exercise: exercise_1632

theorem proof_gap_exercise_1632_1
  (a : ℝ)
  (x : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))
  (h3 : C ∈ (Set.univ : Set ℝ))
  : C ∈ (Set.univ : Set ℝ) := by
  sorry

theorem proof_gap_exercise_1632_2
  (a : ℝ)
  (x : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((a /. x_1) + ((a ^ (2 : ℕ)) /. (x_1 ^ (2 : ℕ)))) + ((a ^ (3 : ℕ)) /. (x_1 ^ (3 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((F_3 x_1) = ((((a * (Real.log |(x_1)|)) - ((a ^ (2 : ℕ)) /. x_1)) - ((a ^ (3 : ℕ)) /. (2 * (x_1 ^ (2 : ℕ))))) + C_1))))))}) := by
  sorry
