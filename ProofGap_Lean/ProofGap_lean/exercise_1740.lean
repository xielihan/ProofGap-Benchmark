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

-- exercise: exercise_1740

theorem proof_gap_exercise_1740_1
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : a ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))
  (h5 : b ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))
  (h6 : |(a)| ≠ |(b)|)
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) * ((x ^ (2 : ℕ)) + (b ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((1 /. ((x ^ (2 : ℕ)) + (b ^ (2 : ℕ)))) - (1 /. ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_4 x) = ((1 /. ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ)))) * (F_3 x)))))))}) := by
  sorry

theorem proof_gap_exercise_1740_2
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : a ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))
  (h5 : b ∈ ((Set.univ : Set ℝ) \ ({x | x = 0})))
  (h6 : |(a)| ≠ |(b)|)
  (h7 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) * ((x ^ (2 : ℕ)) + (b ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((1 /. ((x ^ (2 : ℕ)) + (b ^ (2 : ℕ)))) - (1 /. ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_4 x) = ((1 /. ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ)))) * (F_3 x)))))))}))
  : ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. (((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) * ((x ^ (2 : ℕ)) + (b ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_6 x) = (((1 /. ((a ^ (2 : ℕ)) - (b ^ (2 : ℕ)))) * (((1 /. b) * (Real.arctan (x /. b))) - ((1 /. a) * (Real.arctan (x /. a))))) + C_1))))))}) := by
  sorry
