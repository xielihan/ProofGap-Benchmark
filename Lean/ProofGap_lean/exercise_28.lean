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

-- exercise: exercise_28

theorem proof_gap_exercise_28_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((|((x + 1))| - |((x - 1))|))| < 1)
  : ((x ^ (2 : ℕ)) + (1 /. 2)) < |(((x ^ (2 : ℕ)) - 1))| := by
  sorry

theorem proof_gap_exercise_28_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ((x ^ (2 : ℕ)) + (1 /. 2)) < |(((x ^ (2 : ℕ)) - 1))|)
  : (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))) ∨ (((x ^ (2 : ℕ)) - 1) < (-((x ^ (2 : ℕ)) + (1 /. 2)))) := by
  sorry

theorem proof_gap_exercise_28_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ((x ^ (2 : ℕ)) + (1 /. 2)) < |(((x ^ (2 : ℕ)) - 1))|)
  (h3 : (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))) ∨ (((x ^ (2 : ℕ)) - 1) < (-((x ^ (2 : ℕ)) + (1 /. 2)))))
  : Not (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))) := by
  sorry

theorem proof_gap_exercise_28_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ((x ^ (2 : ℕ)) + (1 /. 2)) < |(((x ^ (2 : ℕ)) - 1))|)
  (h3 : (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))) ∨ (((x ^ (2 : ℕ)) - 1) < (-((x ^ (2 : ℕ)) + (1 /. 2)))))
  (h4 : Not (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))))
  : ((x ^ (2 : ℕ)) - 1) < (-((x ^ (2 : ℕ)) + (1 /. 2))) := by
  sorry

theorem proof_gap_exercise_28_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ((x ^ (2 : ℕ)) + (1 /. 2)) < |(((x ^ (2 : ℕ)) - 1))|)
  (h3 : (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))) ∨ (((x ^ (2 : ℕ)) - 1) < (-((x ^ (2 : ℕ)) + (1 /. 2)))))
  (h4 : Not (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))))
  (h5 : ((x ^ (2 : ℕ)) - 1) < (-((x ^ (2 : ℕ)) + (1 /. 2))))
  : (x ^ (2 : ℕ)) < (1 /. 4) := by
  sorry

theorem proof_gap_exercise_28_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : ((x ^ (2 : ℕ)) + (1 /. 2)) < |(((x ^ (2 : ℕ)) - 1))|)
  (h3 : (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))) ∨ (((x ^ (2 : ℕ)) - 1) < (-((x ^ (2 : ℕ)) + (1 /. 2)))))
  (h4 : Not (((x ^ (2 : ℕ)) - 1) > ((x ^ (2 : ℕ)) + (1 /. 2))))
  (h5 : ((x ^ (2 : ℕ)) - 1) < (-((x ^ (2 : ℕ)) + (1 /. 2))))
  (h6 : (x ^ (2 : ℕ)) < (1 /. 4))
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (|(x_1)| < (1 /. 2))})) ↔ (|((|((x + 1))| - |((x - 1))|))| < 1) := by
  sorry
