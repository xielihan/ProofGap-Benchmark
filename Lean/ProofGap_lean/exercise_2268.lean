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

-- exercise: exercise_2268

theorem proof_gap_exercise_2268_1
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((x * ((2 - (x ^ (2 : ℕ))) ^ (12 : ℕ))) * (1 : ℝ))) = ((-((1 /. 26) * ((2 - ((1 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ)))) - (-((1 /. 26) * ((2 - ((0 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_2268_2
  (h1 : (∫ x in (0 : ℝ)..(1 : ℝ), ((x * ((2 - (x ^ (2 : ℕ))) ^ (12 : ℕ))) * (1 : ℝ))) = ((-((1 /. 26) * ((2 - ((1 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ)))) - (-((1 /. 26) * ((2 - ((0 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ))))))
  (h2 : a = 1)
  : ((-((1 /. 26) * ((2 - ((1 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ)))) - (-((1 /. 26) * ((2 - ((0 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ))))) = (315 /. 26) := by
  sorry

theorem proof_gap_exercise_2268_3
  (h1 : (∫ x in (0 : ℝ)..(1 : ℝ), ((x * ((2 - (x ^ (2 : ℕ))) ^ (12 : ℕ))) * (1 : ℝ))) = ((-((1 /. 26) * ((2 - ((1 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ)))) - (-((1 /. 26) * ((2 - ((0 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ))))))
  (h2 : ((-((1 /. 26) * ((2 - ((1 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ)))) - (-((1 /. 26) * ((2 - ((0 : ℕ) ^ (2 : ℕ))) ^ (13 : ℕ))))) = (315 /. 26))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((x * ((2 - (x ^ (2 : ℕ))) ^ (12 : ℕ))) * (1 : ℝ))) = (315 /. 26) := by
  sorry
