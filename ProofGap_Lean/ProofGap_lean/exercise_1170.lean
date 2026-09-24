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

-- exercise: exercise_1170

theorem proof_gap_exercise_1170_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (((Real.sin x) ^ (2 : ℕ)) * (Real.log x))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → (((y x) = (((1 - (Real.cos (2 * x))) /. 2) * (Real.log x))) ∧ ((((1 - (Real.cos (2 * x))) /. 2) * (Real.log x)) = (((1 /. 2) * (Real.log x)) - (((1 /. 2) * (Real.cos (2 * x))) * (Real.log x))))))) := by
  sorry

theorem proof_gap_exercise_1170_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (((Real.sin x) ^ (2 : ℕ)) * (Real.log x))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → (((y x) = (((1 - (Real.cos (2 * x))) /. 2) * (Real.log x))) ∧ ((((1 - (Real.cos (2 * x))) /. 2) * (Real.log x)) = (((1 /. 2) * (Real.log x)) - (((1 /. 2) * (Real.cos (2 * x))) * (Real.log x))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 6 (fun t => y t) x) = (((((-(1 : ℤ)) ^ (5 : ℕ)) /. 2) * ((((2 * 3) * 4) * 5) /. (x ^ (6 : ℕ)))) - ((1 /. 2) * (iteratedDeriv 6 (fun t => ((Real.cos (2 * t)) * (Real.log t))) x)))))) := by
  sorry

theorem proof_gap_exercise_1170_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (((Real.sin x) ^ (2 : ℕ)) * (Real.log x))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → (((y x) = (((1 - (Real.cos (2 * x))) /. 2) * (Real.log x))) ∧ ((((1 - (Real.cos (2 * x))) /. 2) * (Real.log x)) = (((1 /. 2) * (Real.log x)) - (((1 /. 2) * (Real.cos (2 * x))) * (Real.log x))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 6 (fun t => y t) x) = (((((-(1 : ℤ)) ^ (5 : ℕ)) /. 2) * ((((2 * 3) * 4) * 5) /. (x ^ (6 : ℕ)))) - ((1 /. 2) * (iteratedDeriv 6 (fun t => ((Real.cos (2 * t)) * (Real.log t))) x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((iteratedDeriv 6 (fun t => y t) x) = (((-(60 /. (x ^ (6 : ℕ)))) + ((((144 /. (x ^ (5 : ℕ))) - (160 /. (x ^ (3 : ℕ)))) + (96 /. x)) * (Real.sin (2 * x)))) + (((((60 /. (x ^ (6 : ℕ))) - (180 /. (x ^ (4 : ℕ)))) + (120 /. (x ^ (2 : ℕ)))) + (32 * (Real.log x))) * (Real.cos (2 * x))))))) := by
  sorry
