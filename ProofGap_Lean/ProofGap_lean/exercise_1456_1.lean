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

-- exercise: exercise_1456_1

theorem proof_gap_exercise_1456_1_1
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2) := by
  sorry

theorem proof_gap_exercise_1456_1_2
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}) := by
  sorry

theorem proof_gap_exercise_1456_1_3
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  : (f (-(1 : ℝ))) = (-(2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_1456_1_4
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  : (f 2) = (-(2 : ℝ)) := by
  sorry

theorem proof_gap_exercise_1456_1_5
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  (h5 : (f 2) = (-(2 : ℝ)))
  : (lpMaximumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = 1 ∨ x = (-(2 : ℝ))}) := by
  sorry

theorem proof_gap_exercise_1456_1_6
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  (h5 : (f 2) = (-(2 : ℝ)))
  (h6 : (lpMaximumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = 1 ∨ x = (-(2 : ℝ))}))
  : (f 1) = 2 := by
  sorry

theorem proof_gap_exercise_1456_1_7
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  (h5 : (f 2) = (-(2 : ℝ)))
  (h6 : (lpMaximumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = 1 ∨ x = (-(2 : ℝ))}))
  (h7 : (f 1) = 2)
  : (f (-(2 : ℝ))) = 2 := by
  sorry

theorem proof_gap_exercise_1456_1_8
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  (h5 : (f 2) = (-(2 : ℝ)))
  (h6 : (lpMaximumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = 1 ∨ x = (-(2 : ℝ))}))
  (h7 : (f 1) = 2)
  (h8 : (f (-(2 : ℝ))) = 2)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((-(2 : ℝ)) ≤ (f x)))) := by
  sorry

theorem proof_gap_exercise_1456_1_9
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  (h5 : (f 2) = (-(2 : ℝ)))
  (h6 : (lpMaximumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = 1 ∨ x = (-(2 : ℝ))}))
  (h7 : (f 1) = 2)
  (h8 : (f (-(2 : ℝ))) = 2)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((-(2 : ℝ)) ≤ (f x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((f x) ≤ 2))) := by
  sorry

theorem proof_gap_exercise_1456_1_10
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  (h5 : (f 2) = (-(2 : ℝ)))
  (h6 : (lpMaximumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = 1 ∨ x = (-(2 : ℝ))}))
  (h7 : (f 1) = 2)
  (h8 : (f (-(2 : ℝ))) = 2)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((-(2 : ℝ)) ≤ (f x)))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((f x) ≤ 2))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → (|(((3 * x) - (x ^ (3 : ℕ))))| ≤ 2))) := by
  sorry

theorem proof_gap_exercise_1456_1_11
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  (h5 : (f 2) = (-(2 : ℝ)))
  (h6 : (lpMaximumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = 1 ∨ x = (-(2 : ℝ))}))
  (h7 : (f 1) = 2)
  (h8 : (f (-(2 : ℝ))) = 2)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((-(2 : ℝ)) ≤ (f x)))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((f x) ≤ 2))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → (|(((3 * x) - (x ^ (3 : ℕ))))| ≤ 2))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → (|(((3 * x) - (x ^ (3 : ℕ))))| ≤ 2))) := by
  sorry

theorem proof_gap_exercise_1456_1_12
  (h1 : f = (fun (x : ℝ) => ((3 * x) - (x ^ (3 : ℕ)))))
  (h2 : ContinuousOn f (Set.Icc (-(2 : ℝ)) 2))
  (h3 : (lpMinimumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = (-(1 : ℝ)) ∨ x = 2}))
  (h4 : (f (-(1 : ℝ))) = (-(2 : ℝ)))
  (h5 : (f 2) = (-(2 : ℝ)))
  (h6 : (lpMaximumPointsOn f (Set.Icc (-(2 : ℝ)) 2)) = ({x | x = 1 ∨ x = (-(2 : ℝ))}))
  (h7 : (f 1) = 2)
  (h8 : (f (-(2 : ℝ))) = 2)
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((-(2 : ℝ)) ≤ (f x)))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → ((f x) ≤ 2))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → (|(((3 * x) - (x ^ (3 : ℕ))))| ≤ 2))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → (|(((3 * x) - (x ^ (3 : ℕ))))| ≤ 2))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| ≤ 2)) → (|(((3 * x) - (x ^ (3 : ℕ))))| ≤ 2))) := by
  sorry
