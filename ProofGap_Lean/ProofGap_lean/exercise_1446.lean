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

-- exercise: exercise_1446

theorem proof_gap_exercise_1446_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))) := by
  sorry

theorem proof_gap_exercise_1446_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))) := by
  sorry

theorem proof_gap_exercise_1446_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))) := by
  sorry

theorem proof_gap_exercise_1446_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  : (iteratedDeriv 2 (fun t => f t) 2) = 2 := by
  sorry

theorem proof_gap_exercise_1446_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  (h5 : (iteratedDeriv 2 (fun t => f t) 2) = 2)
  : (iteratedDeriv 2 (fun t => f t) 2) > 0 := by
  sorry

theorem proof_gap_exercise_1446_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  (h5 : (iteratedDeriv 2 (fun t => f t) 2) = 2)
  (h6 : (iteratedDeriv 2 (fun t => f t) 2) > 0)
  : (lpMinimumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 2}) := by
  sorry

theorem proof_gap_exercise_1446_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  (h5 : (iteratedDeriv 2 (fun t => f t) 2) = 2)
  (h6 : (iteratedDeriv 2 (fun t => f t) 2) > 0)
  (h7 : (lpMinimumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 2}))
  : (f (2 : ℝ)) = 2 := by
  sorry

theorem proof_gap_exercise_1446_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  (h5 : (iteratedDeriv 2 (fun t => f t) 2) = 2)
  (h6 : (iteratedDeriv 2 (fun t => f t) 2) > 0)
  (h7 : (lpMinimumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 2}))
  (h8 : (f (2 : ℝ)) = 2)
  : (f (-(3 : ℝ))) = 27 := by
  sorry

theorem proof_gap_exercise_1446_9
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  (h5 : (iteratedDeriv 2 (fun t => f t) 2) = 2)
  (h6 : (iteratedDeriv 2 (fun t => f t) 2) > 0)
  (h7 : (lpMinimumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 2}))
  (h8 : (f (2 : ℝ)) = 2)
  (h9 : (f (-(3 : ℝ))) = 27)
  : (f (10 : ℝ)) = 66 := by
  sorry

theorem proof_gap_exercise_1446_10
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  (h5 : (iteratedDeriv 2 (fun t => f t) 2) = 2)
  (h6 : (iteratedDeriv 2 (fun t => f t) 2) > 0)
  (h7 : (lpMinimumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 2}))
  (h8 : (f (2 : ℝ)) = 2)
  (h9 : (f (-(3 : ℝ))) = 27)
  (h10 : (f (10 : ℝ)) = 66)
  : (max (f (-(3 : ℝ))) (f (10 : ℝ))) = 66 := by
  sorry

theorem proof_gap_exercise_1446_11
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  (h5 : (iteratedDeriv 2 (fun t => f t) 2) = 2)
  (h6 : (iteratedDeriv 2 (fun t => f t) 2) > 0)
  (h7 : (lpMinimumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 2}))
  (h8 : (f (2 : ℝ)) = 2)
  (h9 : (f (-(3 : ℝ))) = 27)
  (h10 : (f (10 : ℝ)) = 66)
  (h11 : (max (f (-(3 : ℝ))) (f (10 : ℝ))) = 66)
  : (lpMaximumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 10}) := by
  sorry

theorem proof_gap_exercise_1446_12
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((x ^ (2 : ℕ)) - (4 * x)) + 6)))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 1 (fun t => f t) x) = ((2 * x) - 4)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc (-(3 : ℝ)) 10))) → ((iteratedDeriv 2 (fun t => f t) x) = 2))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => f t) x) = 0) ↔ (x = 2)))))
  (h5 : (iteratedDeriv 2 (fun t => f t) 2) = 2)
  (h6 : (iteratedDeriv 2 (fun t => f t) 2) > 0)
  (h7 : (lpMinimumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 2}))
  (h8 : (f (2 : ℝ)) = 2)
  (h9 : (f (-(3 : ℝ))) = 27)
  (h10 : (f (10 : ℝ)) = 66)
  (h11 : (max (f (-(3 : ℝ))) (f (10 : ℝ))) = 66)
  (h12 : (lpMaximumPointsOn f (Set.Icc (-(3 : ℝ)) 10)) = ({x | x = 10}))
  : (f (10 : ℝ)) = 66 := by
  sorry
