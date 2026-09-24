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

-- exercise: exercise_1021

theorem proof_gap_exercise_1021_1
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = ((Real.sin (x ^ (2 : ℕ))) /. x))))
  (h2 : x_0 = 0)
  : DifferentiableOn ℝ f (Set.Ioi 0) := by
  sorry

theorem proof_gap_exercise_1021_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = ((Real.sin (x ^ (2 : ℕ))) /. x))))
  (h2 : x_0 = 0)
  (h3 : DifferentiableOn ℝ f (Set.Ioi 0))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * (Real.cos (x ^ (2 : ℕ)))) - ((Real.sin (x ^ (2 : ℕ))) /. (x ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1021_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = ((Real.sin (x ^ (2 : ℕ))) /. x))))
  (h2 : x_0 = 0)
  (h3 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * (Real.cos (x ^ (2 : ℕ)))) - ((Real.sin (x ^ (2 : ℕ))) /. (x ^ (2 : ℕ))))))))
  : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_1021_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = ((Real.sin (x ^ (2 : ℕ))) /. x))))
  (h2 : x_0 = 0)
  (h3 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * (Real.cos (x ^ (2 : ℕ)))) - ((Real.sin (x ^ (2 : ℕ))) /. (x ^ (2 : ℕ))))))))
  (h5 : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0))
  : Not (exists (M : ℝ), ((M ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) atTop (𝓝 M)))) := by
  sorry

theorem proof_gap_exercise_1021_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = ((Real.sin (x ^ (2 : ℕ))) /. x))))
  (h2 : x_0 = 0)
  (h3 : DifferentiableOn ℝ f (Set.Ioi 0))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * (Real.cos (x ^ (2 : ℕ)))) - ((Real.sin (x ^ (2 : ℕ))) /. (x ^ (2 : ℕ))))))))
  (h5 : Tendsto (fun x : ℝ => (f x)) atTop (𝓝 0))
  (h6 : Not (exists (M : ℝ), ((M ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) atTop (𝓝 M)))))
  : Not (forall (f : (ℝ -> ℝ)) (x_0 : ℝ), ((((x_0 ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableOn ℝ f (Set.Ioi x_0))) ∧ (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) atTop (𝓝 L))))) → (exists (M : ℝ), ((M ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) atTop (𝓝 M)))))) := by
  sorry
