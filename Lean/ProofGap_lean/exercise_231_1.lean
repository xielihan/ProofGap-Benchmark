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

-- exercise: exercise_231_1

theorem proof_gap_exercise_231_1_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_231_1_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((3 * (-x)) - ((-x) ^ (3 : ℕ))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_231_1_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((3 * (-x)) - ((-x) ^ (3 : ℕ))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_231_1_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((3 * (-x)) - ((-x) ^ (3 : ℕ))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (-((3 * x) - (x ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_231_1_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((3 * (-x)) - ((-x) ^ (3 : ℕ))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (-((3 * x) - (x ^ (3 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-((3 * x) - (x ^ (3 : ℕ)))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_231_1_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((3 * (-x)) - ((-x) ^ (3 : ℕ))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (-((3 * x) - (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-((3 * x) - (x ^ (3 : ℕ)))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_231_1_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((3 * (-x)) - ((-x) ^ (3 : ℕ))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (-((3 * x) - (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-((3 * x) - (x ^ (3 : ℕ)))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (-(f x))))) := by
  sorry

theorem proof_gap_exercise_231_1_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((3 * (-x)) - ((-x) ^ (3 : ℕ))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (-((3 * x) - (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-((3 * x) - (x ^ (3 : ℕ)))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (-(f x))))))
  : Function.Odd f := by
  sorry

theorem proof_gap_exercise_231_1_9
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((3 * x) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = ((3 * (-x)) - ((-x) ^ (3 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((3 * (-x)) - ((-x) ^ (3 : ℕ))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (-((3 * x) - (x ^ (3 : ℕ))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-((3 * x) - (x ^ (3 : ℕ)))) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((-(f x)) = (((-(3 : ℝ)) * x) + (x ^ (3 : ℕ)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (-x)) = (-(f x))))))
  (h9 : Function.Odd f)
  : Function.Odd f := by
  sorry
