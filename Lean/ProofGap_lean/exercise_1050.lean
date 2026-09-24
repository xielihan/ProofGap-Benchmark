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

-- exercise: exercise_1050

theorem proof_gap_exercise_1050_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : b ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))) + (((y x) ^ (2 : ℕ)) /. (b ^ (2 : ℕ)))) = 1))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * x) /. (a ^ (2 : ℕ))) + (((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x)) /. (b ^ (2 : ℕ)))) = 0))) := by
  sorry

theorem proof_gap_exercise_1050_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a ≠ 0)
  (h4 : b ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ))) + (((y x) ^ (2 : ℕ)) /. (b ^ (2 : ℕ)))) = 1))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * x) /. (a ^ (2 : ℕ))) + (((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x)) /. (b ^ (2 : ℕ)))) = 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((y x) ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (-(((b ^ (2 : ℕ)) * x) /. ((a ^ (2 : ℕ)) * (y x))))))) := by
  sorry
