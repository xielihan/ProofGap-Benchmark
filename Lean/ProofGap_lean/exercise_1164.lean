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

-- exercise: exercise_1164

theorem proof_gap_exercise_1164_1
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = ((Real.log x_1) /. x_1)))))
  : (x > 0) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - (Real.log x)) /. (x ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_1164_2
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = ((Real.log x_1) /. x_1)))))
  (h3 : (x > 0) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - (Real.log x)) /. (x ^ (2 : ℕ)))))
  : (x > 0) → (((iteratedDeriv 2 (fun t => y t) x) = ((((-(1 /. x)) * (x ^ (2 : ℕ))) - ((2 * x) * (1 - (Real.log x)))) /. (x ^ (4 : ℕ)))) ∧ (((((-(1 /. x)) * (x ^ (2 : ℕ))) - ((2 * x) * (1 - (Real.log x)))) /. (x ^ (4 : ℕ))) = (-((3 - (2 * (Real.log x))) /. (x ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1164_3
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = ((Real.log x_1) /. x_1)))))
  (h3 : (x > 0) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - (Real.log x)) /. (x ^ (2 : ℕ)))))
  (h4 : (x > 0) → (((iteratedDeriv 2 (fun t => y t) x) = ((((-(1 /. x)) * (x ^ (2 : ℕ))) - ((2 * x) * (1 - (Real.log x)))) /. (x ^ (4 : ℕ)))) ∧ (((((-(1 /. x)) * (x ^ (2 : ℕ))) - ((2 * x) * (1 - (Real.log x)))) /. (x ^ (4 : ℕ))) = (-((3 - (2 * (Real.log x))) /. (x ^ (3 : ℕ)))))))
  : (x > 0) → (((iteratedDeriv 3 (fun t => y t) x) = (-((((-(2 /. x)) * (x ^ (3 : ℕ))) - ((3 * (x ^ (2 : ℕ))) * (3 - (2 * (Real.log x))))) /. (x ^ (6 : ℕ))))) ∧ ((-((((-(2 /. x)) * (x ^ (3 : ℕ))) - ((3 * (x ^ (2 : ℕ))) * (3 - (2 * (Real.log x))))) /. (x ^ (6 : ℕ)))) = ((11 - (6 * (Real.log x))) /. (x ^ (4 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_1164_4
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = ((Real.log x_1) /. x_1)))))
  (h3 : (x > 0) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - (Real.log x)) /. (x ^ (2 : ℕ)))))
  (h4 : (x > 0) → (((iteratedDeriv 2 (fun t => y t) x) = ((((-(1 /. x)) * (x ^ (2 : ℕ))) - ((2 * x) * (1 - (Real.log x)))) /. (x ^ (4 : ℕ)))) ∧ (((((-(1 /. x)) * (x ^ (2 : ℕ))) - ((2 * x) * (1 - (Real.log x)))) /. (x ^ (4 : ℕ))) = (-((3 - (2 * (Real.log x))) /. (x ^ (3 : ℕ)))))))
  (h5 : (x > 0) → (((iteratedDeriv 3 (fun t => y t) x) = (-((((-(2 /. x)) * (x ^ (3 : ℕ))) - ((3 * (x ^ (2 : ℕ))) * (3 - (2 * (Real.log x))))) /. (x ^ (6 : ℕ))))) ∧ ((-((((-(2 /. x)) * (x ^ (3 : ℕ))) - ((3 * (x ^ (2 : ℕ))) * (3 - (2 * (Real.log x))))) /. (x ^ (6 : ℕ)))) = ((11 - (6 * (Real.log x))) /. (x ^ (4 : ℕ))))))
  : (x > 0) → (((iteratedDeriv 4 (fun t => y t) x) = ((((-(6 /. x)) * (x ^ (4 : ℕ))) - ((4 * (x ^ (3 : ℕ))) * (11 - (6 * (Real.log x))))) /. (x ^ (8 : ℕ)))) ∧ (((((-(6 /. x)) * (x ^ (4 : ℕ))) - ((4 * (x ^ (3 : ℕ))) * (11 - (6 * (Real.log x))))) /. (x ^ (8 : ℕ))) = (-((50 - (24 * (Real.log x))) /. (x ^ (5 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1164_5
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = ((Real.log x_1) /. x_1)))))
  (h3 : (x > 0) → ((iteratedDeriv 1 (fun t => y t) x) = ((1 - (Real.log x)) /. (x ^ (2 : ℕ)))))
  (h4 : (x > 0) → (((iteratedDeriv 2 (fun t => y t) x) = ((((-(1 /. x)) * (x ^ (2 : ℕ))) - ((2 * x) * (1 - (Real.log x)))) /. (x ^ (4 : ℕ)))) ∧ (((((-(1 /. x)) * (x ^ (2 : ℕ))) - ((2 * x) * (1 - (Real.log x)))) /. (x ^ (4 : ℕ))) = (-((3 - (2 * (Real.log x))) /. (x ^ (3 : ℕ)))))))
  (h5 : (x > 0) → (((iteratedDeriv 3 (fun t => y t) x) = (-((((-(2 /. x)) * (x ^ (3 : ℕ))) - ((3 * (x ^ (2 : ℕ))) * (3 - (2 * (Real.log x))))) /. (x ^ (6 : ℕ))))) ∧ ((-((((-(2 /. x)) * (x ^ (3 : ℕ))) - ((3 * (x ^ (2 : ℕ))) * (3 - (2 * (Real.log x))))) /. (x ^ (6 : ℕ)))) = ((11 - (6 * (Real.log x))) /. (x ^ (4 : ℕ))))))
  (h6 : (x > 0) → (((iteratedDeriv 4 (fun t => y t) x) = ((((-(6 /. x)) * (x ^ (4 : ℕ))) - ((4 * (x ^ (3 : ℕ))) * (11 - (6 * (Real.log x))))) /. (x ^ (8 : ℕ)))) ∧ (((((-(6 /. x)) * (x ^ (4 : ℕ))) - ((4 * (x ^ (3 : ℕ))) * (11 - (6 * (Real.log x))))) /. (x ^ (8 : ℕ))) = (-((50 - (24 * (Real.log x))) /. (x ^ (5 : ℕ)))))))
  : (x > 0) → (((iteratedDeriv 5 (fun t => y t) x) = (-((((-(24 /. x)) * (x ^ (5 : ℕ))) - ((5 * (x ^ (4 : ℕ))) * (50 - (24 * (Real.log x))))) /. (x ^ (10 : ℕ))))) ∧ ((-((((-(24 /. x)) * (x ^ (5 : ℕ))) - ((5 * (x ^ (4 : ℕ))) * (50 - (24 * (Real.log x))))) /. (x ^ (10 : ℕ)))) = ((274 - (120 * (Real.log x))) /. (x ^ (6 : ℕ))))) := by
  sorry
