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

-- exercise: exercise_27

theorem proof_gap_exercise_27_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (|((x + 2))| - |(x)|) > 1)
  : (1 + |(x)|) < |((x + 2))| := by
  sorry

theorem proof_gap_exercise_27_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 + |(x)|) < |((x + 2))|)
  : ((1 + |(x)|) ^ (2 : ℕ)) < ((x + 2) ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_27_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 + |(x)|) < |((x + 2))|)
  (h3 : ((1 + |(x)|) ^ (2 : ℕ)) < ((x + 2) ^ (2 : ℕ)))
  : (2 * |(x)|) < ((4 * x) + 3) := by
  sorry

theorem proof_gap_exercise_27_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 + |(x)|) < |((x + 2))|)
  (h3 : ((1 + |(x)|) ^ (2 : ℕ)) < ((x + 2) ^ (2 : ℕ)))
  (h4 : (2 * |(x)|) < ((4 * x) + 3))
  : (4 * (x ^ (2 : ℕ))) < (((4 * x) + 3) ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_27_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 + |(x)|) < |((x + 2))|)
  (h3 : ((1 + |(x)|) ^ (2 : ℕ)) < ((x + 2) ^ (2 : ℕ)))
  (h4 : (2 * |(x)|) < ((4 * x) + 3))
  (h5 : (4 * (x ^ (2 : ℕ))) < (((4 * x) + 3) ^ (2 : ℕ)))
  : (((4 * (x ^ (2 : ℕ))) + (8 * x)) + 3) > 0 := by
  sorry

theorem proof_gap_exercise_27_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 + |(x)|) < |((x + 2))|)
  (h3 : ((1 + |(x)|) ^ (2 : ℕ)) < ((x + 2) ^ (2 : ℕ)))
  (h4 : (2 * |(x)|) < ((4 * x) + 3))
  (h5 : (4 * (x ^ (2 : ℕ))) < (((4 * x) + 3) ^ (2 : ℕ)))
  (h6 : (((4 * (x ^ (2 : ℕ))) + (8 * x)) + 3) > 0)
  : (x > (-(1 /. 2))) ∨ (x < (-(3 /. 2))) := by
  sorry

theorem proof_gap_exercise_27_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 + |(x)|) < |((x + 2))|)
  (h3 : ((1 + |(x)|) ^ (2 : ℕ)) < ((x + 2) ^ (2 : ℕ)))
  (h4 : (2 * |(x)|) < ((4 * x) + 3))
  (h5 : (4 * (x ^ (2 : ℕ))) < (((4 * x) + 3) ^ (2 : ℕ)))
  (h6 : (((4 * (x ^ (2 : ℕ))) + (8 * x)) + 3) > 0)
  (h7 : (x > (-(1 /. 2))) ∨ (x < (-(3 /. 2))))
  : Not (x < (-(3 /. 2))) := by
  sorry

theorem proof_gap_exercise_27_8
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (1 + |(x)|) < |((x + 2))|)
  (h3 : ((1 + |(x)|) ^ (2 : ℕ)) < ((x + 2) ^ (2 : ℕ)))
  (h4 : (2 * |(x)|) < ((4 * x) + 3))
  (h5 : (4 * (x ^ (2 : ℕ))) < (((4 * x) + 3) ^ (2 : ℕ)))
  (h6 : (((4 * (x ^ (2 : ℕ))) + (8 * x)) + 3) > 0)
  (h7 : (x > (-(1 /. 2))) ∨ (x < (-(3 /. 2))))
  (h8 : Not (x < (-(3 /. 2))))
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > (-(1 /. 2)))})) ↔ ((|((x + 2))| - |(x)|) > 1) := by
  sorry
