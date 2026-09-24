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

-- exercise: exercise_948

theorem proof_gap_exercise_948_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (x ≠ ((((2 * k) - 1) /. 2) * Real.pi))))) → ((y x) = (Real.arctan ((Real.tan x) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (x ≠ ((((2 * k) - 1) /. 2) * Real.pi))))) → ((iteratedDeriv 1 (fun t => y t) x) = ((((1 /. (1 + ((Real.tan x) ^ (4 : ℕ)))) * 2) * (Real.tan x)) * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_948_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (x ≠ ((((2 * k) - 1) /. 2) * Real.pi))))) → ((y x) = (Real.arctan ((Real.tan x) ^ (2 : ℕ)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (x ≠ ((((2 * k) - 1) /. 2) * Real.pi))))) → ((iteratedDeriv 1 (fun t => y t) x) = ((((1 /. (1 + ((Real.tan x) ^ (4 : ℕ)))) * 2) * (Real.tan x)) * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (x ≠ ((((2 * k) - 1) /. 2) * Real.pi))))) → ((iteratedDeriv 1 (fun t => y t) x) = ((Real.sin (2 * x)) /. (((Real.sin x) ^ (4 : ℕ)) + ((Real.cos x) ^ (4 : ℕ))))))) := by
  sorry
