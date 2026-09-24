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

-- exercise: exercise_1396_1

theorem proof_gap_exercise_1396_1_1
  : (Real.rpow (30 : ℝ) (((3 : ℝ))⁻¹)) = (3 * (Real.rpow (1 + (1 /. 9)) (1 /. 3))) := by
  sorry

theorem proof_gap_exercise_1396_1_2
  (h1 : (Real.rpow (30 : ℝ) (((3 : ℝ))⁻¹)) = (3 * (Real.rpow (1 + (1 /. 9)) (1 /. 3))))
  : |((Real.rpow (1 + (1 /. 9)) (1 /. 3)) - ((1 + ((1 /. 3) * (1 /. 9))) + ((((1 /. 3) * ((1 /. 3) - 1)) /. ((2 : ℕ))!) * ((1 /. 9) ^ (2 : ℕ)))))| ≤ ((3 * ((((1 /. 3) * (2 /. 3)) * (5 /. 3)) /. ((3 : ℕ))!)) * ((1 /. 9) ^ (3 : ℕ))) := by
  sorry

theorem proof_gap_exercise_1396_1_3
  (h1 : (Real.rpow (30 : ℝ) (((3 : ℝ))⁻¹)) = (3 * (Real.rpow (1 + (1 /. 9)) (1 /. 3))))
  (h2 : |((Real.rpow (1 + (1 /. 9)) (1 /. 3)) - ((1 + ((1 /. 3) * (1 /. 9))) + ((((1 /. 3) * ((1 /. 3) - 1)) /. ((2 : ℕ))!) * ((1 /. 9) ^ (2 : ℕ)))))| ≤ ((3 * ((((1 /. 3) * (2 /. 3)) * (5 /. 3)) /. ((3 : ℕ))!)) * ((1 /. 9) ^ (3 : ℕ))))
  : |((Real.rpow (30 : ℝ) (((3 : ℝ))⁻¹)) - (((31070 : ℝ) /. (10000 : ℝ))))| ≤ ((((254 : ℝ) /. (100 : ℝ))) * ((10 : ℝ) ^ (-(4 : ℤ)))) := by
  sorry
