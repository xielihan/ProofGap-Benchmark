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

-- exercise: exercise_1165

theorem proof_gap_exercise_1165_1
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ (2 : ℕ)) * (Real.sin (2 * x_1)))))))
  : (iteratedDeriv 50 (fun t => y t) x) = ((((x ^ (2 : ℕ)) * (iteratedDeriv 50 (fun t => (Real.sin (2 * t))) x)) + ((((Nat.choose (50 : ℕ) (1 : ℕ)) * 2) * x) * (iteratedDeriv 49 (fun t => (Real.sin (2 * t))) x))) + ((2 * (Nat.choose (50 : ℕ) (2 : ℕ))) * (iteratedDeriv 48 (fun t => (Real.sin (2 * t))) x))) := by
  sorry

theorem proof_gap_exercise_1165_2
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ (2 : ℕ)) * (Real.sin (2 * x_1)))))))
  (h3 : (iteratedDeriv 50 (fun t => y t) x) = ((((x ^ (2 : ℕ)) * (iteratedDeriv 50 (fun t => (Real.sin (2 * t))) x)) + ((((Nat.choose (50 : ℕ) (1 : ℕ)) * 2) * x) * (iteratedDeriv 49 (fun t => (Real.sin (2 * t))) x))) + ((2 * (Nat.choose (50 : ℕ) (2 : ℕ))) * (iteratedDeriv 48 (fun t => (Real.sin (2 * t))) x))))
  : (iteratedDeriv 50 (fun t => y t) x) = ((((((2 : ℕ) ^ (50 : ℕ)) * (x ^ (2 : ℕ))) * (Real.sin ((2 * x) + ((50 /. 2) * Real.pi)))) + (((100 * x) * ((2 : ℕ) ^ (49 : ℕ))) * (Real.sin ((2 * x) + ((49 /. 2) * Real.pi))))) + ((((50 * 49) /. (1 * 2)) * ((2 : ℕ) ^ (49 : ℕ))) * (Real.sin ((2 * x) + ((48 /. 2) * Real.pi))))) := by
  sorry

theorem proof_gap_exercise_1165_3
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ (2 : ℕ)) * (Real.sin (2 * x_1)))))))
  (h3 : (iteratedDeriv 50 (fun t => y t) x) = ((((x ^ (2 : ℕ)) * (iteratedDeriv 50 (fun t => (Real.sin (2 * t))) x)) + ((((Nat.choose (50 : ℕ) (1 : ℕ)) * 2) * x) * (iteratedDeriv 49 (fun t => (Real.sin (2 * t))) x))) + ((2 * (Nat.choose (50 : ℕ) (2 : ℕ))) * (iteratedDeriv 48 (fun t => (Real.sin (2 * t))) x))))
  (h4 : (iteratedDeriv 50 (fun t => y t) x) = ((((((2 : ℕ) ^ (50 : ℕ)) * (x ^ (2 : ℕ))) * (Real.sin ((2 * x) + ((50 /. 2) * Real.pi)))) + (((100 * x) * ((2 : ℕ) ^ (49 : ℕ))) * (Real.sin ((2 * x) + ((49 /. 2) * Real.pi))))) + ((((50 * 49) /. (1 * 2)) * ((2 : ℕ) ^ (49 : ℕ))) * (Real.sin ((2 * x) + ((48 /. 2) * Real.pi))))))
  : (iteratedDeriv 50 (fun t => y t) x) = (((2 : ℕ) ^ (50 : ℕ)) * ((((-(x ^ (2 : ℕ))) * (Real.sin (2 * x))) + ((50 * x) * (Real.cos (2 * x)))) + ((1225 /. 2) * (Real.sin (2 * x))))) := by
  sorry
