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

-- exercise: exercise_835

theorem proof_gap_exercise_835_1
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((((x_1 ^ (3 : ℕ)) /. 3) + ((x_1 ^ (2 : ℕ)) /. 2)) - (2 * x_1))))))
  : (iteratedDeriv 1 (fun t => y t) x) = (((x ^ (2 : ℕ)) + x) - 2) := by
  sorry

theorem proof_gap_exercise_835_2
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((((x_1 ^ (3 : ℕ)) /. 3) + ((x_1 ^ (2 : ℕ)) /. 2)) - (2 * x_1))))))
  (h3 : (iteratedDeriv 1 (fun t => y t) x) = (((x ^ (2 : ℕ)) + x) - 2))
  : ((iteratedDeriv 1 (fun t => y t) x) = 0) → ((((x ^ (2 : ℕ)) + x) - 2) = 0) := by
  sorry

theorem proof_gap_exercise_835_3
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((((x_1 ^ (3 : ℕ)) /. 3) + ((x_1 ^ (2 : ℕ)) /. 2)) - (2 * x_1))))))
  (h3 : (iteratedDeriv 1 (fun t => y t) x) = (((x ^ (2 : ℕ)) + x) - 2))
  (h4 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → ((((x ^ (2 : ℕ)) + x) - 2) = 0))
  : ((iteratedDeriv 1 (fun t => y t) x) = 0) → (x ∈ ({x | x = (-(2 : ℝ)) ∨ x = 1})) := by
  sorry

theorem proof_gap_exercise_835_4
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((((x_1 ^ (3 : ℕ)) /. 3) + ((x_1 ^ (2 : ℕ)) /. 2)) - (2 * x_1))))))
  (h3 : (iteratedDeriv 1 (fun t => y t) x) = (((x ^ (2 : ℕ)) + x) - 2))
  (h4 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → ((((x ^ (2 : ℕ)) + x) - 2) = 0))
  (h5 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → (x ∈ ({x | x = (-(2 : ℝ)) ∨ x = 1})))
  : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (((x ^ (2 : ℕ)) + x) = 0) := by
  sorry

theorem proof_gap_exercise_835_5
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((((x_1 ^ (3 : ℕ)) /. 3) + ((x_1 ^ (2 : ℕ)) /. 2)) - (2 * x_1))))))
  (h3 : (iteratedDeriv 1 (fun t => y t) x) = (((x ^ (2 : ℕ)) + x) - 2))
  (h4 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → ((((x ^ (2 : ℕ)) + x) - 2) = 0))
  (h5 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → (x ∈ ({x | x = (-(2 : ℝ)) ∨ x = 1})))
  (h6 : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (((x ^ (2 : ℕ)) + x) = 0))
  : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0})) := by
  sorry

theorem proof_gap_exercise_835_6
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((((x_1 ^ (3 : ℕ)) /. 3) + ((x_1 ^ (2 : ℕ)) /. 2)) - (2 * x_1))))))
  (h3 : (iteratedDeriv 1 (fun t => y t) x) = (((x ^ (2 : ℕ)) + x) - 2))
  (h4 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → ((((x ^ (2 : ℕ)) + x) - 2) = 0))
  (h5 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → (x ∈ ({x | x = (-(2 : ℝ)) ∨ x = 1})))
  (h6 : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (((x ^ (2 : ℕ)) + x) = 0))
  (h7 : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0})))
  : ((iteratedDeriv 1 (fun t => y t) x) = 10) → ((((x ^ (2 : ℕ)) + x) - 12) = 0) := by
  sorry

theorem proof_gap_exercise_835_7
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((((x_1 ^ (3 : ℕ)) /. 3) + ((x_1 ^ (2 : ℕ)) /. 2)) - (2 * x_1))))))
  (h3 : (iteratedDeriv 1 (fun t => y t) x) = (((x ^ (2 : ℕ)) + x) - 2))
  (h4 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → ((((x ^ (2 : ℕ)) + x) - 2) = 0))
  (h5 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → (x ∈ ({x | x = (-(2 : ℝ)) ∨ x = 1})))
  (h6 : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (((x ^ (2 : ℕ)) + x) = 0))
  (h7 : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0})))
  (h8 : ((iteratedDeriv 1 (fun t => y t) x) = 10) → ((((x ^ (2 : ℕ)) + x) - 12) = 0))
  : ((iteratedDeriv 1 (fun t => y t) x) = 10) → (x ∈ ({x | x = (-(4 : ℝ)) ∨ x = 3})) := by
  sorry

theorem proof_gap_exercise_835_8
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((((x_1 ^ (3 : ℕ)) /. 3) + ((x_1 ^ (2 : ℕ)) /. 2)) - (2 * x_1))))))
  (h3 : (iteratedDeriv 1 (fun t => y t) x) = (((x ^ (2 : ℕ)) + x) - 2))
  (h4 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → ((((x ^ (2 : ℕ)) + x) - 2) = 0))
  (h5 : ((iteratedDeriv 1 (fun t => y t) x) = 0) → (x ∈ ({x | x = (-(2 : ℝ)) ∨ x = 1})))
  (h6 : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (((x ^ (2 : ℕ)) + x) = 0))
  (h7 : ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0})))
  (h8 : ((iteratedDeriv 1 (fun t => y t) x) = 10) → ((((x ^ (2 : ℕ)) + x) - 12) = 0))
  (h9 : ((iteratedDeriv 1 (fun t => y t) x) = 10) → (x ∈ ({x | x = (-(4 : ℝ)) ∨ x = 3})))
  : (((((iteratedDeriv 1 (fun t => y t) x) = 0) → (x ∈ ({x | x = (-(2 : ℝ)) ∨ x = 1}))) ∧ (((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ))) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0})))) ∧ (((iteratedDeriv 1 (fun t => y t) x) = 10) → (x ∈ ({x | x = (-(4 : ℝ)) ∨ x = 3})))) ↔ ((((iteratedDeriv 1 (fun t => y t) x) = 0) ∨ ((iteratedDeriv 1 (fun t => y t) x) = (-(2 : ℝ)))) ∨ ((iteratedDeriv 1 (fun t => y t) x) = 10)) := by
  sorry
