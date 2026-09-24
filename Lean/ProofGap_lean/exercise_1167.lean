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

-- exercise: exercise_1167

theorem proof_gap_exercise_1167_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((1 /. 4) * (Real.sin (4 * x))) - ((1 /. 4) * (Real.sin (6 * x)))) + ((1 /. 4) * (Real.sin (2 * x))))))) := by
  sorry

theorem proof_gap_exercise_1167_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((1 /. 4) * (Real.sin (4 * x))) - ((1 /. 4) * (Real.sin (6 * x)))) + ((1 /. 4) * (Real.sin (2 * x))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 10 (fun t => y t) x) = (((((1 /. 4) * ((4 : ℕ) ^ (10 : ℕ))) * (Real.sin ((4 * x) + ((10 /. 2) * Real.pi)))) - (((1 /. 4) * ((6 : ℕ) ^ (10 : ℕ))) * (Real.sin ((6 * x) + ((10 /. 2) * Real.pi))))) + (((1 /. 4) * ((2 : ℕ) ^ (10 : ℕ))) * (Real.sin ((2 * x) + ((10 /. 2) * Real.pi)))))))) := by
  sorry

theorem proof_gap_exercise_1167_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (((Real.sin x) * (Real.sin (2 * x))) * (Real.sin (3 * x)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((((1 /. 4) * (Real.sin (4 * x))) - ((1 /. 4) * (Real.sin (6 * x)))) + ((1 /. 4) * (Real.sin (2 * x))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 10 (fun t => y t) x) = (((((1 /. 4) * ((4 : ℕ) ^ (10 : ℕ))) * (Real.sin ((4 * x) + ((10 /. 2) * Real.pi)))) - (((1 /. 4) * ((6 : ℕ) ^ (10 : ℕ))) * (Real.sin ((6 * x) + ((10 /. 2) * Real.pi))))) + (((1 /. 4) * ((2 : ℕ) ^ (10 : ℕ))) * (Real.sin ((2 * x) + ((10 /. 2) * Real.pi)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 10 (fun t => y t) x) = ((((-((2 : ℝ) ^ (18 : ℕ))) * (Real.sin (4 * x))) + ((((2 : ℕ) ^ (8 : ℕ)) * ((3 : ℕ) ^ (10 : ℕ))) * (Real.sin (6 * x)))) - (((2 : ℕ) ^ (8 : ℕ)) * (Real.sin (2 * x))))))) := by
  sorry
