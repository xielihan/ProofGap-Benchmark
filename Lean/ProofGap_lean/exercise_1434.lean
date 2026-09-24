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

-- exercise: exercise_1434

theorem proof_gap_exercise_1434_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((y x) = ((((x ^ (2 : ℕ)) - (3 * x)) + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 1))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((5 * x) - 7) /. ((x + 1) ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1434_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((y x) = ((((x ^ (2 : ℕ)) - (3 * x)) + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 1))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((5 * x) - 7) /. ((x + 1) ^ (3 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (7 /. 5))))) := by
  sorry

theorem proof_gap_exercise_1434_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((y x) = ((((x ^ (2 : ℕ)) - (3 * x)) + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 1))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((5 * x) - 7) /. ((x + 1) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (7 /. 5))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < (7 /. 5))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1434_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((y x) = ((((x ^ (2 : ℕ)) - (3 * x)) + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 1))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((5 * x) - 7) /. ((x + 1) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (7 /. 5))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < (7 /. 5))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > (7 /. 5))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1434_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((y x) = ((((x ^ (2 : ℕ)) - (3 * x)) + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 1))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((5 * x) - 7) /. ((x + 1) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (7 /. 5))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < (7 /. 5))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > (7 /. 5))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (lpMinimumPoints y) = ({x | x = (7 /. 5)}) := by
  sorry

theorem proof_gap_exercise_1434_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((y x) = ((((x ^ (2 : ℕ)) - (3 * x)) + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 1))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((5 * x) - 7) /. ((x + 1) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = (7 /. 5))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < (7 /. 5))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > (7 /. 5))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (lpMinimumPoints y) = ({x | x = (7 /. 5)}))
  : (y (7 /. 5)) = (-(1 /. 24)) := by
  sorry
