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

-- exercise: exercise_1156

theorem proof_gap_exercise_1156_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x * (((2 * x) - 1) ^ (2 : ℕ))) * ((x + 3) ^ (3 : ℕ)))))))
  : (fun (x1 : ℝ) => (iteratedDeriv 6 (fun t => y t) x1)) = (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!) := by
  sorry

theorem proof_gap_exercise_1156_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x * (((2 * x) - 1) ^ (2 : ℕ))) * ((x + 3) ^ (3 : ℕ)))))))
  (h2 : (fun (x1 : ℝ) => (iteratedDeriv 6 (fun t => y t) x1)) = (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!))
  : (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!) = (4 * ((6 : ℕ))!) := by
  sorry

theorem proof_gap_exercise_1156_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x * (((2 * x) - 1) ^ (2 : ℕ))) * ((x + 3) ^ (3 : ℕ)))))))
  (h2 : (fun (x1 : ℝ) => (iteratedDeriv 6 (fun t => y t) x1)) = (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!))
  (h3 : (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!) = (4 * ((6 : ℕ))!))
  : (4 * ((6 : ℕ))!) = 2880 := by
  sorry

theorem proof_gap_exercise_1156_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x * (((2 * x) - 1) ^ (2 : ℕ))) * ((x + 3) ^ (3 : ℕ)))))))
  (h2 : (fun (x1 : ℝ) => (iteratedDeriv 6 (fun t => y t) x1)) = (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!))
  (h3 : (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!) = (4 * ((6 : ℕ))!))
  (h4 : (4 * ((6 : ℕ))!) = 2880)
  : (fun (x1 : ℝ) => (iteratedDeriv 6 (fun t => y t) x1)) = 2880 := by
  sorry

theorem proof_gap_exercise_1156_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x * (((2 * x) - 1) ^ (2 : ℕ))) * ((x + 3) ^ (3 : ℕ)))))))
  (h2 : (fun (x1 : ℝ) => (iteratedDeriv 6 (fun t => y t) x1)) = (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!))
  (h3 : (((1 * ((2 : ℕ) ^ (2 : ℕ))) * ((1 : ℕ) ^ (3 : ℕ))) * ((6 : ℕ))!) = (4 * ((6 : ℕ))!))
  (h4 : (4 * ((6 : ℕ))!) = 2880)
  (h5 : (fun (x1 : ℝ) => (iteratedDeriv 6 (fun t => y t) x1)) = 2880)
  : (fun (x1 : ℝ) => (iteratedDeriv 7 (fun t => y t) x1)) = 0 := by
  sorry
