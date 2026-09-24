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

-- exercise: exercise_2480_1

theorem proof_gap_exercise_2480_1_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (V_x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : V_x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : V_x = ((5 * (Real.pi ^ (2 : ℕ))) * (a ^ (3 : ℕ))))
  : V_x = (Real.pi * (∫ t in (0 : ℝ)..(2 * Real.pi), (((a ^ (3 : ℕ)) * ((1 - (Real.cos t)) ^ (3 : ℕ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2480_1_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (V_x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : V_x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : V_x = (Real.pi * (∫ t in (0 : ℝ)..(2 * Real.pi), (((a ^ (3 : ℕ)) * ((1 - (Real.cos t)) ^ (3 : ℕ))) * (1 : ℝ)))))
  : V_x = ((5 * (Real.pi ^ (2 : ℕ))) * (a ^ (3 : ℕ))) := by
  sorry
