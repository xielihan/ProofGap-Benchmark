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

-- exercise: exercise_1086

theorem proof_gap_exercise_1086_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((1 /. a) * (Real.arctan (x_1 /. a)))))))
  : (iteratedDeriv 1 (fun t => y t) x) = (((1 /. a) * (1 /. a)) * (1 /. (1 + ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1086_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((1 /. a) * (Real.arctan (x_1 /. a)))))))
  (h4 : (iteratedDeriv 1 (fun t => y t) x) = (((1 /. a) * (1 /. a)) * (1 /. (1 + ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))))
  : (iteratedDeriv 1 (fun t => y t) x) = (1 /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_1086_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((1 /. a) * (Real.arctan (x_1 /. a)))))))
  (h4 : (iteratedDeriv 1 (fun t => y t) x) = (((1 /. a) * (1 /. a)) * (1 /. (1 + ((x ^ (2 : ℕ)) /. (a ^ (2 : ℕ)))))))
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (1 /. ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ)))))
  : (fderiv ℝ y) = ((fun (x_1 : ℝ) => (1 /. ((a ^ (2 : ℕ)) + (x_1 ^ (2 : ℕ))))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) := by
  sorry
