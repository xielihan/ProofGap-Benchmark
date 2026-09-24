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

-- exercise: exercise_1395

theorem proof_gap_exercise_1395_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  : |(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| ≤ ((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!) := by
  sorry

theorem proof_gap_exercise_1395_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| ≤ ((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!))
  : (((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!) < (((00001 : ℝ) /. (10000 : ℝ)))) → (|(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| < (((00001 : ℝ) /. (10000 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_1395_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| ≤ ((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!))
  (h3 : (((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!) < (((00001 : ℝ) /. (10000 : ℝ)))) → (|(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| < (((00001 : ℝ) /. (10000 : ℝ)))))
  : (|(x)| < (((022134 : ℝ) /. (100000 : ℝ)))) → (((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!) < (((00001 : ℝ) /. (10000 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_1395_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| ≤ ((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!))
  (h3 : (((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!) < (((00001 : ℝ) /. (10000 : ℝ)))) → (|(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| < (((00001 : ℝ) /. (10000 : ℝ)))))
  (h4 : (|(x)| < (((022134 : ℝ) /. (100000 : ℝ)))) → (((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!) < (((00001 : ℝ) /. (10000 : ℝ)))))
  : (|(x)| < (((022134 : ℝ) /. (100000 : ℝ)))) → (|(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| < (((00001 : ℝ) /. (10000 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_1395_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| ≤ ((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!))
  (h3 : (((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!) < (((00001 : ℝ) /. (10000 : ℝ)))) → (|(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| < (((00001 : ℝ) /. (10000 : ℝ)))))
  (h4 : (|(x)| < (((022134 : ℝ) /. (100000 : ℝ)))) → (((|(x)| ^ (4 : ℕ)) /. ((4 : ℕ))!) < (((00001 : ℝ) /. (10000 : ℝ)))))
  (h5 : (|(x)| < (((022134 : ℝ) /. (100000 : ℝ)))) → (|(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| < (((00001 : ℝ) /. (10000 : ℝ)))))
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < (((022134 : ℝ) /. (100000 : ℝ))))})) ↔ (|(((Real.cos x) - (1 - ((x ^ (2 : ℕ)) /. 2))))| < (((00001 : ℝ) /. (10000 : ℝ)))) := by
  sorry
