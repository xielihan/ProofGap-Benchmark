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

-- exercise: exercise_534

theorem proof_gap_exercise_534_1
  : Tendsto (fun x : ℝ => (Real.logb 10 ((100 + (x ^ (2 : ℕ))) /. (1 + (100 * (x ^ (2 : ℕ))))))) atTop (𝓝 (Real.logb 10 (1 /. 100))) := by
  sorry

theorem proof_gap_exercise_534_2
  (h1 : Tendsto (fun x : ℝ => (Real.logb 10 ((100 + (x ^ (2 : ℕ))) /. (1 + (100 * (x ^ (2 : ℕ))))))) atTop (𝓝 (Real.logb 10 (1 /. 100))))
  : (Real.logb 10 (1 /. 100)) = (-(2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_534_3
  (h1 : Tendsto (fun x : ℝ => (Real.logb 10 ((100 + (x ^ (2 : ℕ))) /. (1 + (100 * (x ^ (2 : ℕ))))))) atTop (𝓝 (Real.logb 10 (1 /. 100))))
  (h2 : (Real.logb 10 (1 /. 100)) = (-(2 : ℝ)))
  : Tendsto (fun x : ℝ => (Real.logb 10 ((100 + (x ^ (2 : ℕ))) /. (1 + (100 * (x ^ (2 : ℕ))))))) atTop (𝓝 (-(2 : ℝ))) := by
  sorry
