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

-- exercise: exercise_3122

theorem proof_gap_exercise_3122_1
  (y : (ℝ -> ℝ))
  (x_0 : ℝ)
  (h : ℝ)
  (y_Neg_1 : ℝ)
  (y_0 : ℝ)
  (y_1 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0))
  (h3 : y_Neg_1 ∈ (Set.univ : Set ℝ))
  (h4 : y_0 ∈ (Set.univ : Set ℝ))
  (h5 : y_1 ∈ (Set.univ : Set ℝ))
  (h6 : (y (x_0 - h)) = y_Neg_1)
  (h7 : (y x_0) = y_0)
  (h8 : (y (x_0 + h)) = y_1)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((((x - x_0) * ((x - x_0) - h)) /. (((x_0 - h) - x_0) * ((x_0 - h) - (x_0 + h)))) * y_Neg_1) + (((((x - x_0) + h) * ((x - x_0) - h)) /. ((x_0 - (x_0 - h)) * (x_0 - (x_0 + h)))) * y_0)) + (((((x - x_0) + h) * (x - x_0)) /. (((x_0 + h) - (x_0 - h)) * ((x_0 + h) - x_0))) * y_1))))) := by
  sorry

theorem proof_gap_exercise_3122_2
  (y : (ℝ -> ℝ))
  (x_0 : ℝ)
  (h : ℝ)
  (y_Neg_1 : ℝ)
  (y_0 : ℝ)
  (y_1 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0))
  (h3 : y_Neg_1 ∈ (Set.univ : Set ℝ))
  (h4 : y_0 ∈ (Set.univ : Set ℝ))
  (h5 : y_1 ∈ (Set.univ : Set ℝ))
  (h6 : (y (x_0 - h)) = y_Neg_1)
  (h7 : (y x_0) = y_0)
  (h8 : (y (x_0 + h)) = y_1)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((((x - x_0) * ((x - x_0) - h)) /. (((x_0 - h) - x_0) * ((x_0 - h) - (x_0 + h)))) * y_Neg_1) + (((((x - x_0) + h) * ((x - x_0) - h)) /. ((x_0 - (x_0 - h)) * (x_0 - (x_0 + h)))) * y_0)) + (((((x - x_0) + h) * (x - x_0)) /. (((x_0 + h) - (x_0 - h)) * ((x_0 + h) - x_0))) * y_1))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((y_0 + (((y_1 - y_Neg_1) /. (2 * h)) * (x - x_0))) + ((((y_1 - (2 * y_0)) + y_Neg_1) /. (2 * (h ^ (2 : ℕ)))) * ((x - x_0) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3122_3
  (y : (ℝ -> ℝ))
  (x_0 : ℝ)
  (h : ℝ)
  (y_Neg_1 : ℝ)
  (y_0 : ℝ)
  (y_1 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0))
  (h3 : y_Neg_1 ∈ (Set.univ : Set ℝ))
  (h4 : y_0 ∈ (Set.univ : Set ℝ))
  (h5 : y_1 ∈ (Set.univ : Set ℝ))
  (h6 : (y (x_0 - h)) = y_Neg_1)
  (h7 : (y x_0) = y_0)
  (h8 : (y (x_0 + h)) = y_1)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((((x - x_0) * ((x - x_0) - h)) /. (((x_0 - h) - x_0) * ((x_0 - h) - (x_0 + h)))) * y_Neg_1) + (((((x - x_0) + h) * ((x - x_0) - h)) /. ((x_0 - (x_0 - h)) * (x_0 - (x_0 + h)))) * y_0)) + (((((x - x_0) + h) * (x - x_0)) /. (((x_0 + h) - (x_0 - h)) * ((x_0 + h) - x_0))) * y_1))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((y_0 + (((y_1 - y_Neg_1) /. (2 * h)) * (x - x_0))) + ((((y_1 - (2 * y_0)) + y_Neg_1) /. (2 * (h ^ (2 : ℕ)))) * ((x - x_0) ^ (2 : ℕ))))))))
  : (exists (a : ℝ) (b : ℝ) (c : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (b ∈ (Set.univ : Set ℝ))) ∧ (c ∈ (Set.univ : Set ℝ))) ∧ ((forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((y_0 + (((y_1 - y_Neg_1) /. (2 * h)) * (x - x_0))) + ((((y_1 - (2 * y_0)) + y_Neg_1) /. (2 * (h ^ (2 : ℕ)))) * ((x - x_0) ^ (2 : ℕ))))))) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((a * (x ^ (2 : ℕ))) + (b * x)) + c))))))) := by
  sorry
