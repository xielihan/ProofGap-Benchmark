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

-- exercise: exercise_1204

theorem proof_gap_exercise_1204_1
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((x ^ (2 : ℕ)) + (2 * x)) + 2) * (Real.exp (-x)))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ n) * (((x ^ (2 : ℕ)) + (2 * x)) + 2)) * (Real.exp (-x))) + ((((2 * ((-(1 : ℤ)) ^ (n - 1))) * (x + 1)) * (Real.exp (-x))) * n)) + (((((-(1 : ℤ)) ^ (n - 2)) * n) * (n - 1)) * (Real.exp (-x))))))) := by
  sorry

theorem proof_gap_exercise_1204_2
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((x ^ (2 : ℕ)) + (2 * x)) + 2) * (Real.exp (-x)))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ n) * (((x ^ (2 : ℕ)) + (2 * x)) + 2)) * (Real.exp (-x))) + ((((2 * ((-(1 : ℤ)) ^ (n - 1))) * (x + 1)) * (Real.exp (-x))) * n)) + (((((-(1 : ℤ)) ^ (n - 2)) * n) * (n - 1)) * (Real.exp (-x))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv n (fun t => y t) x) = ((((-(1 : ℤ)) ^ n) * (Real.exp (-x))) * (((x ^ (2 : ℕ)) - ((2 * (n - 1)) * x)) + ((n - 1) * (n - 2))))))) := by
  sorry
