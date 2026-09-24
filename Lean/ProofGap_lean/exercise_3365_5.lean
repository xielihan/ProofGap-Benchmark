import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_3365_5

theorem proof_gap_exercise_3365_5_1
  (y : (ℝ -> ℝ))
  (v_uCE_uB4 : ℝ)
  (h1 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB4 > 0)
  (h3 : v_uCE_uB4 < 1)
  (h4 : ContinuousOn y (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4)))
  (h5 : (y (1 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4)))) → (((y x) ^ (2 : ℕ)) = (x ^ (2 : ℕ))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4)))) → ((y x) = x))) := by
  sorry

theorem proof_gap_exercise_3365_5_2
  (y : (ℝ -> ℝ))
  (v_uCE_uB4 : ℝ)
  (h1 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB4 > 0)
  (h3 : v_uCE_uB4 < 1)
  (h4 : ContinuousOn y (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4)))
  (h5 : (y (1 : ℝ)) = 1)
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4)))) → (((y x) ^ (2 : ℕ)) = (x ^ (2 : ℕ))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4)))) → ((y x) = x))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4))))) → (((y : ℝ → _) x) = x)) ↔ (((ContinuousOn y (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4))) ∧ ((y (1 : ℝ)) = 1)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (1 - v_uCE_uB4) (1 + v_uCE_uB4)))) → (((y x) ^ (2 : ℕ)) = (x ^ (2 : ℕ)))))) := by
  sorry
