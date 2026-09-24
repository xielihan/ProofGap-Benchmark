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

-- exercise: exercise_902

theorem proof_gap_exercise_902_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (Real.log (Real.tan ((x /. 2) + (Real.pi /. 4))))))))
  : (forall (x : ℝ) (k : ℤ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (|((x - ((2 * k) * Real.pi)))| < (Real.pi /. 2))) → (((((iteratedDeriv 1 (fun t => y t) x) = (((1 /. (Real.tan ((x /. 2) + (Real.pi /. 4)))) * (((1 : ℝ) /. (Real.cos ((x /. 2) + (Real.pi /. 4)))) ^ (2 : ℕ))) * (1 /. 2))) ∧ ((((1 /. (Real.tan ((x /. 2) + (Real.pi /. 4)))) * (((1 : ℝ) /. (Real.cos ((x /. 2) + (Real.pi /. 4)))) ^ (2 : ℕ))) * (1 /. 2)) = (1 /. ((2 * (Real.sin ((x /. 2) + (Real.pi /. 4)))) * (Real.cos ((x /. 2) + (Real.pi /. 4))))))) ∧ ((1 /. ((2 * (Real.sin ((x /. 2) + (Real.pi /. 4)))) * (Real.cos ((x /. 2) + (Real.pi /. 4))))) = (1 /. (Real.sin (x + (Real.pi /. 2)))))) ∧ ((1 /. (Real.sin (x + (Real.pi /. 2)))) = (1 /. (Real.cos x)))))) := by
  sorry
