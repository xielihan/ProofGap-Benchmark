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

-- exercise: exercise_193

theorem proof_gap_exercise_193_1
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((f x_1) = ((1 - x_1) /. (1 + x_1))))))
  : (f (0 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_193_2
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((f x_1) = ((1 - x_1) /. (1 + x_1))))))
  (h3 : (f (0 : ℝ)) = 1)
  : (x ≠ 1) → ((f (-x)) = ((1 + x) /. (1 - x))) := by
  sorry

theorem proof_gap_exercise_193_3
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((f x_1) = ((1 - x_1) /. (1 + x_1))))))
  (h3 : (f (0 : ℝ)) = 1)
  (h4 : (x ≠ 1) → ((f (-x)) = ((1 + x) /. (1 - x))))
  : (x ≠ (-(2 : ℝ))) → (((f (x + 1)) = ((1 - (x + 1)) /. ((1 + x) + 1))) ∧ (((1 - (x + 1)) /. ((1 + x) + 1)) = (-(x /. (x + 2))))) := by
  sorry

theorem proof_gap_exercise_193_4
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((f x_1) = ((1 - x_1) /. (1 + x_1))))))
  (h3 : (f (0 : ℝ)) = 1)
  (h4 : (x ≠ 1) → ((f (-x)) = ((1 + x) /. (1 - x))))
  (h5 : (x ≠ (-(2 : ℝ))) → (((f (x + 1)) = ((1 - (x + 1)) /. ((1 + x) + 1))) ∧ (((1 - (x + 1)) /. ((1 + x) + 1)) = (-(x /. (x + 2))))))
  : (x ≠ (-(1 : ℝ))) → ((((f x) + 1) = (((1 - x) /. (1 + x)) + 1)) ∧ ((((1 - x) /. (1 + x)) + 1) = (2 /. (1 + x)))) := by
  sorry

theorem proof_gap_exercise_193_5
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((f x_1) = ((1 - x_1) /. (1 + x_1))))))
  (h3 : (f (0 : ℝ)) = 1)
  (h4 : (x ≠ 1) → ((f (-x)) = ((1 + x) /. (1 - x))))
  (h5 : (x ≠ (-(2 : ℝ))) → (((f (x + 1)) = ((1 - (x + 1)) /. ((1 + x) + 1))) ∧ (((1 - (x + 1)) /. ((1 + x) + 1)) = (-(x /. (x + 2))))))
  (h6 : (x ≠ (-(1 : ℝ))) → ((((f x) + 1) = (((1 - x) /. (1 + x)) + 1)) ∧ ((((1 - x) /. (1 + x)) + 1) = (2 /. (1 + x)))))
  : ((x ≠ 0) ∧ (x ≠ (-(1 : ℝ)))) → (((f (1 /. x)) = ((1 - (1 /. x)) /. (1 + (1 /. x)))) ∧ (((1 - (1 /. x)) /. (1 + (1 /. x))) = ((x - 1) /. (x + 1)))) := by
  sorry

theorem proof_gap_exercise_193_6
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((f x_1) = ((1 - x_1) /. (1 + x_1))))))
  (h3 : (f (0 : ℝ)) = 1)
  (h4 : (x ≠ 1) → ((f (-x)) = ((1 + x) /. (1 - x))))
  (h5 : (x ≠ (-(2 : ℝ))) → (((f (x + 1)) = ((1 - (x + 1)) /. ((1 + x) + 1))) ∧ (((1 - (x + 1)) /. ((1 + x) + 1)) = (-(x /. (x + 2))))))
  (h6 : (x ≠ (-(1 : ℝ))) → ((((f x) + 1) = (((1 - x) /. (1 + x)) + 1)) ∧ ((((1 - x) /. (1 + x)) + 1) = (2 /. (1 + x)))))
  (h7 : ((x ≠ 0) ∧ (x ≠ (-(1 : ℝ)))) → (((f (1 /. x)) = ((1 - (1 /. x)) /. (1 + (1 /. x)))) ∧ (((1 - (1 /. x)) /. (1 + (1 /. x))) = ((x - 1) /. (x + 1)))))
  : ((x ≠ (-(1 : ℝ))) ∧ (x ≠ 1)) → (((1 /. (f x)) = (1 /. ((1 - x) /. (1 + x)))) ∧ ((1 /. ((1 - x) /. (1 + x))) = ((1 + x) /. (1 - x)))) := by
  sorry
