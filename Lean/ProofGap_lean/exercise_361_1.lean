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

-- exercise: exercise_361_1

theorem proof_gap_exercise_361_1_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ (Set.univ : Set ℝ))
  (h4 : y_0 ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((a * x) + b)))))
  : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → ((y x_0_1) = ((a * x_0_1) + b)))) := by
  sorry

theorem proof_gap_exercise_361_1_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ (Set.univ : Set ℝ))
  (h4 : y_0 ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((a * x) + b)))))
  (h6 : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → ((y x_0_1) = ((a * x_0_1) + b)))))
  : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((((y (x_0_1 + t)) + (y (x_0_1 - t))) = ((((a * (x_0_1 + t)) + b) + (a * (x_0_1 - t))) + b)) ∧ (((((a * (x_0_1 + t)) + b) + (a * (x_0_1 - t))) + b) = (2 * ((a * x_0_1) + b)))))))) := by
  sorry

theorem proof_gap_exercise_361_1_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ (Set.univ : Set ℝ))
  (h4 : y_0 ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((a * x) + b)))))
  (h6 : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → ((y x_0_1) = ((a * x_0_1) + b)))))
  (h7 : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((((y (x_0_1 + t)) + (y (x_0_1 - t))) = ((((a * (x_0_1 + t)) + b) + (a * (x_0_1 - t))) + b)) ∧ (((((a * (x_0_1 + t)) + b) + (a * (x_0_1 - t))) + b) = (2 * ((a * x_0_1) + b)))))))))
  : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0_1 + t)) + (y (x_0_1 - t))) = (2 * (y x_0_1))))))) := by
  sorry

theorem proof_gap_exercise_361_1_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (x_0 : ℝ)
  (y_0 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x_0 ∈ (Set.univ : Set ℝ))
  (h4 : y_0 ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((a * x) + b)))))
  (h6 : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → ((y x_0_1) = ((a * x_0_1) + b)))))
  (h7 : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((((y (x_0_1 + t)) + (y (x_0_1 - t))) = ((((a * (x_0_1 + t)) + b) + (a * (x_0_1 - t))) + b)) ∧ (((((a * (x_0_1 + t)) + b) + (a * (x_0_1 - t))) + b) = (2 * ((a * x_0_1) + b)))))))))
  (h8 : (forall (x_0_1 : ℝ), ((x_0_1 ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0_1 + t)) + (y (x_0_1 - t))) = (2 * (y x_0_1))))))))
  : ((x_0, y_0) ∈ ({p | p = (x_0, ((a * x_0) + b)) ∧ (x_0 ∈ (Set.univ : Set ℝ))})) ↔ (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((y (x_0 + t)) + (y (x_0 - t))) = (2 * y_0)))) := by
  sorry
