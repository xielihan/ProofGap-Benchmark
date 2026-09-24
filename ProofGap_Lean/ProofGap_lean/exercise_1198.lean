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

-- exercise: exercise_1198

theorem proof_gap_exercise_1198_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((Real.cos (a * x)) * (Real.cos (b * x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((1 /. 2) * (Real.cos ((a - b) * x))) + ((1 /. 2) * (Real.cos ((a + b) * x))))))) := by
  sorry

theorem proof_gap_exercise_1198_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((Real.cos (a * x)) * (Real.cos (b * x)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((1 /. 2) * (Real.cos ((a - b) * x))) + ((1 /. 2) * (Real.cos ((a + b) * x))))))))
  : (fun (x1 : ℝ) => (iteratedDeriv n (fun t => y t) x1)) = (fun (x : ℝ) => ((((1 /. 2) * ((a - b) ^ n)) * (Real.cos (((a - b) * x) + ((n /. 2) * Real.pi)))) + (((1 /. 2) * ((a + b) ^ n)) * (Real.cos (((a + b) * x) + ((n /. 2) * Real.pi)))))) := by
  sorry
