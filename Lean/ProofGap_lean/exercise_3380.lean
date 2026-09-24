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

-- exercise: exercise_3380

theorem proof_gap_exercise_3380_1
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0 := by
  sorry

theorem proof_gap_exercise_3380_2
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))) := by
  sorry

theorem proof_gap_exercise_3380_3
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3380_4
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h6 : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))))
  : (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3380_5
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h6 : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))))
  (h7 : (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3380_6
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h6 : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))))
  (h7 : (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h8 : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  : (iteratedDeriv 3 (fun t => y t) x) = ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))) := by
  sorry

theorem proof_gap_exercise_3380_7
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h6 : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))))
  (h7 : (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h8 : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h9 : (iteratedDeriv 3 (fun t => y t) x) = ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))))
  : ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3380_8
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h6 : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))))
  (h7 : (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h8 : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h9 : (iteratedDeriv 3 (fun t => y t) x) = ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))))
  (h10 : ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))))
  : (iteratedDeriv 3 (fun t => y t) x) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3380_9
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h6 : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))))
  (h7 : (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h8 : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h9 : (iteratedDeriv 3 (fun t => y t) x) = ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))))
  (h10 : ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))))
  (h11 : (iteratedDeriv 3 (fun t => y t) x) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))))
  : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))) := by
  sorry

theorem proof_gap_exercise_3380_10
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h6 : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))))
  (h7 : (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h8 : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h9 : (iteratedDeriv 3 (fun t => y t) x) = ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))))
  (h10 : ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))))
  (h11 : (iteratedDeriv 3 (fun t => y t) x) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))))
  (h12 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3380_11
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ContDiff ℝ (3 : ℕ∞) y)
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((((x_1 ^ (2 : ℕ)) + (x_1 * (y x_1))) + ((y x_1) ^ (2 : ℕ))) = 3) ∧ ((x_1 + (2 * (y x_1))) ≠ 0)))))
  (h4 : ((((2 * x) + (y x)) + (x * (iteratedDeriv 1 (fun t => y t) x))) + ((2 * (y x)) * (iteratedDeriv 1 (fun t => y t) x))) = 0)
  (h5 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h6 : (iteratedDeriv 2 (fun t => y t) x) = (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))))
  (h7 : (-((((2 + (iteratedDeriv 1 (fun t => y t) x)) * (x + (2 * (y x)))) - ((1 + (2 * (iteratedDeriv 1 (fun t => y t) x))) * ((2 * x) + (y x)))) /. ((x + (2 * (y x))) ^ (2 : ℕ)))) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h8 : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  (h9 : (iteratedDeriv 3 (fun t => y t) x) = ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))))
  (h10 : ((54 /. ((x + (2 * (y x))) ^ (4 : ℕ))) * (1 + (2 * (iteratedDeriv 1 (fun t => y t) x)))) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))))
  (h11 : (iteratedDeriv 3 (fun t => y t) x) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))))
  (h12 : (iteratedDeriv 1 (fun t => y t) x) = (-(((2 * x) + (y x)) /. (x + (2 * (y x))))))
  (h13 : (iteratedDeriv 2 (fun t => y t) x) = (-(18 /. ((x + (2 * (y x))) ^ (3 : ℕ)))))
  : (iteratedDeriv 3 (fun t => y t) x) = (-((162 * x) /. ((x + (2 * (y x))) ^ (5 : ℕ)))) := by
  sorry
