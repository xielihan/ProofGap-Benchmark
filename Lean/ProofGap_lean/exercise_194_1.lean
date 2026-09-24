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

-- exercise: exercise_194_1

theorem proof_gap_exercise_194_1_1
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (x_1 - (x_1 ^ (3 : ℕ)))))))
  : (f x) = (x - (x ^ (3 : ℕ))) := by
  sorry

theorem proof_gap_exercise_194_1_2
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (x_1 - (x_1 ^ (3 : ℕ)))))))
  (h3 : (f x) = (x - (x ^ (3 : ℕ))))
  : (x - (x ^ (3 : ℕ))) = ((x * (1 - x)) * (1 + x)) := by
  sorry

theorem proof_gap_exercise_194_1_3
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (x_1 - (x_1 ^ (3 : ℕ)))))))
  (h3 : (f x) = (x - (x ^ (3 : ℕ))))
  (h4 : (x - (x ^ (3 : ℕ))) = ((x * (1 - x)) * (1 + x)))
  : (f x) = ((x * (1 - x)) * (1 + x)) := by
  sorry

theorem proof_gap_exercise_194_1_4
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (x_1 - (x_1 ^ (3 : ℕ)))))))
  (h3 : (f x) = (x - (x ^ (3 : ℕ))))
  (h4 : (x - (x ^ (3 : ℕ))) = ((x * (1 - x)) * (1 + x)))
  (h5 : (f x) = ((x * (1 - x)) * (1 + x)))
  : ((f x) = 0) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0 ∨ x = 1})) := by
  sorry

theorem proof_gap_exercise_194_1_5
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (x_1 - (x_1 ^ (3 : ℕ)))))))
  (h3 : (f x) = (x - (x ^ (3 : ℕ))))
  (h4 : (x - (x ^ (3 : ℕ))) = ((x * (1 - x)) * (1 + x)))
  (h5 : (f x) = ((x * (1 - x)) * (1 + x)))
  (h6 : ((f x) = 0) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0 ∨ x = 1})))
  : ((f x) > 0) → (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((⊥ < (x_1 : EReal)) ∧ (x_1 < (-(1 : ℝ)))) ∨ ((0 < x_1) ∧ (x_1 < 1)))})) := by
  sorry

theorem proof_gap_exercise_194_1_6
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (x_1 - (x_1 ^ (3 : ℕ)))))))
  (h3 : (f x) = (x - (x ^ (3 : ℕ))))
  (h4 : (x - (x ^ (3 : ℕ))) = ((x * (1 - x)) * (1 + x)))
  (h5 : (f x) = ((x * (1 - x)) * (1 + x)))
  (h6 : ((f x) = 0) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0 ∨ x = 1})))
  (h7 : ((f x) > 0) → (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((⊥ < (x_1 : EReal)) ∧ (x_1 < (-(1 : ℝ)))) ∨ ((0 < x_1) ∧ (x_1 < 1)))})))
  : ((f x) < 0) → (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((((-(1 : ℝ)) < x_1) ∧ (x_1 < 0)) ∨ ((1 < x_1) ∧ ((x_1 : EReal) < ⊤)))})) := by
  sorry

theorem proof_gap_exercise_194_1_7
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((f x_1) = (x_1 - (x_1 ^ (3 : ℕ)))))))
  (h3 : (f x) = (x - (x ^ (3 : ℕ))))
  (h4 : (x - (x ^ (3 : ℕ))) = ((x * (1 - x)) * (1 + x)))
  (h5 : (f x) = ((x * (1 - x)) * (1 + x)))
  (h6 : ((f x) = 0) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0 ∨ x = 1})))
  (h7 : ((f x) > 0) → (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((⊥ < (x_1 : EReal)) ∧ (x_1 < (-(1 : ℝ)))) ∨ ((0 < x_1) ∧ (x_1 < 1)))})))
  (h8 : ((f x) < 0) → (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((((-(1 : ℝ)) < x_1) ∧ (x_1 < 0)) ∨ ((1 < x_1) ∧ ((x_1 : EReal) < ⊤)))})))
  : (((((f x) = 0) → (x ∈ ({x | x = (-(1 : ℝ)) ∨ x = 0 ∨ x = 1}))) ∧ (((f x) > 0) → (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((⊥ < (x_1 : EReal)) ∧ (x_1 < (-(1 : ℝ)))) ∨ ((0 < x_1) ∧ (x_1 < 1)))})))) ∧ (((f x) < 0) → (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((((-(1 : ℝ)) < x_1) ∧ (x_1 < 0)) ∨ ((1 < x_1) ∧ ((x_1 : EReal) < ⊤)))})))) ↔ ((x ∈ (Set.univ : Set ℝ)) ∧ ((((f x) = 0) ∨ ((f x) > 0)) ∨ ((f x) < 0))) := by
  sorry
