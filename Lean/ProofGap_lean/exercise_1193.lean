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

-- exercise: exercise_1193

theorem proof_gap_exercise_1193_1
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((Real.sin x) ^ (2 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = ((2 * (Real.sin x)) * (Real.cos x))) ∧ (((2 * (Real.sin x)) * (Real.cos x)) = (Real.sin (2 * x)))))) := by
  sorry

theorem proof_gap_exercise_1193_2
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((Real.sin x) ^ (2 : ℕ))))))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = ((2 * (Real.sin x)) * (Real.cos x))) ∧ (((2 * (Real.sin x)) * (Real.cos x)) = (Real.sin (2 * x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((iteratedDeriv n (fun t => y t) x) = (iteratedDeriv ((1 + n) - 1) (fun t => y t) x)) ∧ ((iteratedDeriv ((1 + n) - 1) (fun t => y t) x) = (iteratedDeriv (n - 1) (fun t => (Real.sin (2 * t))) x))) ∧ ((iteratedDeriv (n - 1) (fun t => (Real.sin (2 * t))) x) = (((2 : ℕ) ^ (n - 1)) * (Real.sin ((2 * x) + (((n - 1) /. 2) * Real.pi)))))) ∧ ((((2 : ℕ) ^ (n - 1)) * (Real.sin ((2 * x) + (((n - 1) /. 2) * Real.pi)))) = ((-((2 : ℝ) ^ (n - 1))) * (Real.cos ((2 * x) + ((n /. 2) * Real.pi)))))))) := by
  sorry
