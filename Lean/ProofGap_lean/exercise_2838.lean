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

-- exercise: exercise_2838

theorem proof_gap_exercise_2838_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_2838_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((((x + 1) ^ (3 : ℕ)) - (3 * ((x + 1) ^ (2 : ℕ)))) + (3 * (x + 1))) - 1)))) := by
  sorry

theorem proof_gap_exercise_2838_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((((x + 1) ^ (3 : ℕ)) - (3 * ((x + 1) ^ (2 : ℕ)))) + (3 * (x + 1))) - 1)))))
  : (f (-(1 : ℝ))) = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_2838_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((((x + 1) ^ (3 : ℕ)) - (3 * ((x + 1) ^ (2 : ℕ)))) + (3 * (x + 1))) - 1)))))
  (h4 : (f (-(1 : ℝ))) = (-(1 : ℝ)))
  : (iteratedDeriv 1 (fun t => f t) (-(1 : ℝ))) = 3 := by
  sorry

theorem proof_gap_exercise_2838_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((((x + 1) ^ (3 : ℕ)) - (3 * ((x + 1) ^ (2 : ℕ)))) + (3 * (x + 1))) - 1)))))
  (h4 : (f (-(1 : ℝ))) = (-(1 : ℝ)))
  (h5 : (iteratedDeriv 1 (fun t => f t) (-(1 : ℝ))) = 3)
  : (iteratedDeriv 2 (fun t => f t) (-(1 : ℝ))) = (-(6 : ℝ)) := by
  sorry

theorem proof_gap_exercise_2838_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((((x + 1) ^ (3 : ℕ)) - (3 * ((x + 1) ^ (2 : ℕ)))) + (3 * (x + 1))) - 1)))))
  (h4 : (f (-(1 : ℝ))) = (-(1 : ℝ)))
  (h5 : (iteratedDeriv 1 (fun t => f t) (-(1 : ℝ))) = 3)
  (h6 : (iteratedDeriv 2 (fun t => f t) (-(1 : ℝ))) = (-(6 : ℝ)))
  : (iteratedDeriv 3 (fun t => f t) (-(1 : ℝ))) = 6 := by
  sorry

theorem proof_gap_exercise_2838_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((((x + 1) ^ (3 : ℕ)) - (3 * ((x + 1) ^ (2 : ℕ)))) + (3 * (x + 1))) - 1)))))
  (h4 : (f (-(1 : ℝ))) = (-(1 : ℝ)))
  (h5 : (iteratedDeriv 1 (fun t => f t) (-(1 : ℝ))) = 3)
  (h6 : (iteratedDeriv 2 (fun t => f t) (-(1 : ℝ))) = (-(6 : ℝ)))
  (h7 : (iteratedDeriv 3 (fun t => f t) (-(1 : ℝ))) = 6)
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 4)) → ((iteratedDeriv n (fun t => f t) (-(1 : ℝ))) = 0))) := by
  sorry

theorem proof_gap_exercise_2838_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((((x + 1) ^ (3 : ℕ)) - (3 * ((x + 1) ^ (2 : ℕ)))) + (3 * (x + 1))) - 1)))))
  (h4 : (f (-(1 : ℝ))) = (-(1 : ℝ)))
  (h5 : (iteratedDeriv 1 (fun t => f t) (-(1 : ℝ))) = 3)
  (h6 : (iteratedDeriv 2 (fun t => f t) (-(1 : ℝ))) = (-(6 : ℝ)))
  (h7 : (iteratedDeriv 3 (fun t => f t) (-(1 : ℝ))) = 6)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 4)) → ((iteratedDeriv n (fun t => f t) (-(1 : ℝ))) = 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((((-(1 : ℝ)) + (3 * (x + 1))) - ((6 /. ((2 : ℕ))!) * ((x + 1) ^ (2 : ℕ)))) + ((6 /. ((3 : ℕ))!) * ((x + 1) ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_2838_9
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x + 1) - 1) ^ (3 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((((x + 1) ^ (3 : ℕ)) - (3 * ((x + 1) ^ (2 : ℕ)))) + (3 * (x + 1))) - 1)))))
  (h4 : (f (-(1 : ℝ))) = (-(1 : ℝ)))
  (h5 : (iteratedDeriv 1 (fun t => f t) (-(1 : ℝ))) = 3)
  (h6 : (iteratedDeriv 2 (fun t => f t) (-(1 : ℝ))) = (-(6 : ℝ)))
  (h7 : (iteratedDeriv 3 (fun t => f t) (-(1 : ℝ))) = 6)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 4)) → ((iteratedDeriv n (fun t => f t) (-(1 : ℝ))) = 0))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((((-(1 : ℝ)) + (3 * (x + 1))) - ((6 /. ((2 : ℕ))!) * ((x + 1) ^ (2 : ℕ)))) + ((6 /. ((3 : ℕ))!) * ((x + 1) ^ (3 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((((-(1 : ℝ)) + (3 * (x + 1))) - (3 * ((x + 1) ^ (2 : ℕ)))) + ((x + 1) ^ (3 : ℕ)))))) := by
  sorry
