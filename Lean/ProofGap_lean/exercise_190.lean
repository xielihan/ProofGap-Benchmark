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

-- exercise: exercise_190

theorem proof_gap_exercise_190_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_190_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  (h2 : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)))
  : (Real.logb 10 (1 : ℝ)) = 0 := by
  sorry

theorem proof_gap_exercise_190_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  (h2 : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)))
  (h3 : (Real.logb 10 (1 : ℝ)) = 0)
  : (f (-(1 : ℝ))) = 0 := by
  sorry

theorem proof_gap_exercise_190_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  (h2 : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)))
  (h3 : (Real.logb 10 (1 : ℝ)) = 0)
  (h4 : (f (-(1 : ℝ))) = 0)
  : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_190_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  (h2 : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)))
  (h3 : (Real.logb 10 (1 : ℝ)) = 0)
  (h4 : (f (-(1 : ℝ))) = 0)
  (h5 : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))))
  : (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))) = (-(6 : ℝ)) := by
  sorry

theorem proof_gap_exercise_190_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  (h2 : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)))
  (h3 : (Real.logb 10 (1 : ℝ)) = 0)
  (h4 : (f (-(1 : ℝ))) = 0)
  (h5 : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))))
  (h6 : (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))) = (-(6 : ℝ)))
  : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (-(6 : ℝ)) := by
  sorry

theorem proof_gap_exercise_190_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  (h2 : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)))
  (h3 : (Real.logb 10 (1 : ℝ)) = 0)
  (h4 : (f (-(1 : ℝ))) = 0)
  (h5 : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))))
  (h6 : (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))) = (-(6 : ℝ)))
  (h7 : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (-(6 : ℝ)))
  : (f (100 : ℝ)) = (Real.logb 10 (10000 : ℝ)) := by
  sorry

theorem proof_gap_exercise_190_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  (h2 : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)))
  (h3 : (Real.logb 10 (1 : ℝ)) = 0)
  (h4 : (f (-(1 : ℝ))) = 0)
  (h5 : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))))
  (h6 : (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))) = (-(6 : ℝ)))
  (h7 : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (-(6 : ℝ)))
  (h8 : (f (100 : ℝ)) = (Real.logb 10 (10000 : ℝ)))
  : (Real.logb 10 (10000 : ℝ)) = 4 := by
  sorry

theorem proof_gap_exercise_190_9
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = (Real.logb 10 (x ^ (2 : ℕ)))))))
  (h2 : (f (-(1 : ℝ))) = (Real.logb 10 (1 : ℝ)))
  (h3 : (Real.logb 10 (1 : ℝ)) = 0)
  (h4 : (f (-(1 : ℝ))) = 0)
  (h5 : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))))
  (h6 : (Real.logb 10 (((0000001 : ℝ) /. (1000000 : ℝ)))) = (-(6 : ℝ)))
  (h7 : (f (-(((0001 : ℝ) /. (1000 : ℝ))))) = (-(6 : ℝ)))
  (h8 : (f (100 : ℝ)) = (Real.logb 10 (10000 : ℝ)))
  (h9 : (Real.logb 10 (10000 : ℝ)) = 4)
  : (f (100 : ℝ)) = 4 := by
  sorry
