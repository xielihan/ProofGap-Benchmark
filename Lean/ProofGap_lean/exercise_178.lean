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

-- exercise: exercise_178

theorem proof_gap_exercise_178_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  : ContinuousOn y (Set.Icc 1 2) := by
  sorry

theorem proof_gap_exercise_178_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : ContinuousOn y (Set.Icc 1 2))
  : MonotoneOn y (Set.Icc 1 2) := by
  sorry

theorem proof_gap_exercise_178_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : ContinuousOn y (Set.Icc 1 2))
  (h3 : MonotoneOn y (Set.Icc 1 2))
  : (lpMinimumPointsOn y (Set.Icc 1 2)) = ({x | x = 1}) := by
  sorry

theorem proof_gap_exercise_178_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : ContinuousOn y (Set.Icc 1 2))
  (h3 : MonotoneOn y (Set.Icc 1 2))
  (h4 : (lpMinimumPointsOn y (Set.Icc 1 2)) = ({x | x = 1}))
  : (y (1 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_178_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : ContinuousOn y (Set.Icc 1 2))
  (h3 : MonotoneOn y (Set.Icc 1 2))
  (h4 : (lpMinimumPointsOn y (Set.Icc 1 2)) = ({x | x = 1}))
  (h5 : (y (1 : ℝ)) = 1)
  : (lpMaximumPointsOn y (Set.Icc 1 2)) = ({x | x = 2}) := by
  sorry

theorem proof_gap_exercise_178_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : ContinuousOn y (Set.Icc 1 2))
  (h3 : MonotoneOn y (Set.Icc 1 2))
  (h4 : (lpMinimumPointsOn y (Set.Icc 1 2)) = ({x | x = 1}))
  (h5 : (y (1 : ℝ)) = 1)
  (h6 : (lpMaximumPointsOn y (Set.Icc 1 2)) = ({x | x = 2}))
  : (y (2 : ℝ)) = 4 := by
  sorry

theorem proof_gap_exercise_178_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x ^ (2 : ℕ))))))
  (h2 : ContinuousOn y (Set.Icc 1 2))
  (h3 : MonotoneOn y (Set.Icc 1 2))
  (h4 : (lpMinimumPointsOn y (Set.Icc 1 2)) = ({x | x = 1}))
  (h5 : (y (1 : ℝ)) = 1)
  (h6 : (lpMaximumPointsOn y (Set.Icc 1 2)) = ({x | x = 2}))
  (h7 : (y (2 : ℝ)) = 4)
  : (y '' (Set.Icc 1 2)) = (Set.Icc 1 4) := by
  sorry
