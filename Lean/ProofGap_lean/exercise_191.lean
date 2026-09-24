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

-- exercise: exercise_191

theorem proof_gap_exercise_191_1
  (f : (ℝ -> ℤ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (1 + ⌊x⌋)))))
  : ⌊(((09 : ℝ) /. (10 : ℝ)))⌋ = 0 := by
  sorry

theorem proof_gap_exercise_191_2
  (f : (ℝ -> ℤ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (1 + ⌊x⌋)))))
  (h2 : ⌊(((09 : ℝ) /. (10 : ℝ)))⌋ = 0)
  : ⌊(((099 : ℝ) /. (100 : ℝ)))⌋ = 0 := by
  sorry

theorem proof_gap_exercise_191_3
  (f : (ℝ -> ℤ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (1 + ⌊x⌋)))))
  (h2 : ⌊(((09 : ℝ) /. (10 : ℝ)))⌋ = 0)
  (h3 : ⌊(((099 : ℝ) /. (100 : ℝ)))⌋ = 0)
  : ⌊(((0999 : ℝ) /. (1000 : ℝ)))⌋ = 0 := by
  sorry

theorem proof_gap_exercise_191_4
  (f : (ℝ -> ℤ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (1 + ⌊x⌋)))))
  (h2 : ⌊(((09 : ℝ) /. (10 : ℝ)))⌋ = 0)
  (h3 : ⌊(((099 : ℝ) /. (100 : ℝ)))⌋ = 0)
  (h4 : ⌊(((0999 : ℝ) /. (1000 : ℝ)))⌋ = 0)
  : ⌊(1 : ℝ)⌋ = 1 := by
  sorry

theorem proof_gap_exercise_191_5
  (f : (ℝ -> ℤ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (1 + ⌊x⌋)))))
  (h2 : ⌊(((09 : ℝ) /. (10 : ℝ)))⌋ = 0)
  (h3 : ⌊(((099 : ℝ) /. (100 : ℝ)))⌋ = 0)
  (h4 : ⌊(((0999 : ℝ) /. (1000 : ℝ)))⌋ = 0)
  (h5 : ⌊(1 : ℝ)⌋ = 1)
  : (f (((09 : ℝ) /. (10 : ℝ)))) = 1 := by
  sorry

theorem proof_gap_exercise_191_6
  (f : (ℝ -> ℤ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (1 + ⌊x⌋)))))
  (h2 : ⌊(((09 : ℝ) /. (10 : ℝ)))⌋ = 0)
  (h3 : ⌊(((099 : ℝ) /. (100 : ℝ)))⌋ = 0)
  (h4 : ⌊(((0999 : ℝ) /. (1000 : ℝ)))⌋ = 0)
  (h5 : ⌊(1 : ℝ)⌋ = 1)
  (h6 : (f (((09 : ℝ) /. (10 : ℝ)))) = 1)
  : (f (((099 : ℝ) /. (100 : ℝ)))) = 1 := by
  sorry

theorem proof_gap_exercise_191_7
  (f : (ℝ -> ℤ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (1 + ⌊x⌋)))))
  (h2 : ⌊(((09 : ℝ) /. (10 : ℝ)))⌋ = 0)
  (h3 : ⌊(((099 : ℝ) /. (100 : ℝ)))⌋ = 0)
  (h4 : ⌊(((0999 : ℝ) /. (1000 : ℝ)))⌋ = 0)
  (h5 : ⌊(1 : ℝ)⌋ = 1)
  (h6 : (f (((09 : ℝ) /. (10 : ℝ)))) = 1)
  (h7 : (f (((099 : ℝ) /. (100 : ℝ)))) = 1)
  : (f (((0999 : ℝ) /. (1000 : ℝ)))) = 1 := by
  sorry

theorem proof_gap_exercise_191_8
  (f : (ℝ -> ℤ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (1 + ⌊x⌋)))))
  (h2 : ⌊(((09 : ℝ) /. (10 : ℝ)))⌋ = 0)
  (h3 : ⌊(((099 : ℝ) /. (100 : ℝ)))⌋ = 0)
  (h4 : ⌊(((0999 : ℝ) /. (1000 : ℝ)))⌋ = 0)
  (h5 : ⌊(1 : ℝ)⌋ = 1)
  (h6 : (f (((09 : ℝ) /. (10 : ℝ)))) = 1)
  (h7 : (f (((099 : ℝ) /. (100 : ℝ)))) = 1)
  (h8 : (f (((0999 : ℝ) /. (1000 : ℝ)))) = 1)
  : (f (1 : ℝ)) = 2 := by
  sorry
