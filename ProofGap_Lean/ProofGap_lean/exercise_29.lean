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

-- exercise: exercise_29

theorem proof_gap_exercise_29_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((x * (1 - x)))| < (((005 : ℝ) /. (100 : ℝ))))
  : |((x - (x ^ (2 : ℕ))))| < (1 /. 20) := by
  sorry

theorem proof_gap_exercise_29_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((x - (x ^ (2 : ℕ))))| < (1 /. 20))
  : (((x ^ (2 : ℕ)) - x) + (1 /. 20)) > 0 := by
  sorry

theorem proof_gap_exercise_29_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((x - (x ^ (2 : ℕ))))| < (1 /. 20))
  (h3 : (((x ^ (2 : ℕ)) - x) + (1 /. 20)) > 0)
  : (((x ^ (2 : ℕ)) - x) - (1 /. 20)) < 0 := by
  sorry

theorem proof_gap_exercise_29_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((x - (x ^ (2 : ℕ))))| < (1 /. 20))
  (h3 : (((x ^ (2 : ℕ)) - x) + (1 /. 20)) > 0)
  (h4 : (((x ^ (2 : ℕ)) - x) - (1 /. 20)) < 0)
  : (((5 + (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x) ∨ (x < ((5 - (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10)) := by
  sorry

theorem proof_gap_exercise_29_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((x - (x ^ (2 : ℕ))))| < (1 /. 20))
  (h3 : (((x ^ (2 : ℕ)) - x) + (1 /. 20)) > 0)
  (h4 : (((x ^ (2 : ℕ)) - x) - (1 /. 20)) < 0)
  (h5 : (((5 + (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x) ∨ (x < ((5 - (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10)))
  : ((5 - (Real.rpow (30 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x := by
  sorry

theorem proof_gap_exercise_29_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((x - (x ^ (2 : ℕ))))| < (1 /. 20))
  (h3 : (((x ^ (2 : ℕ)) - x) + (1 /. 20)) > 0)
  (h4 : (((x ^ (2 : ℕ)) - x) - (1 /. 20)) < 0)
  (h5 : (((5 + (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x) ∨ (x < ((5 - (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10)))
  (h6 : ((5 - (Real.rpow (30 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x)
  : x < ((5 + (Real.rpow (30 : ℝ) (((2 : ℝ))⁻¹))) /. 10) := by
  sorry

theorem proof_gap_exercise_29_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |((x - (x ^ (2 : ℕ))))| < (1 /. 20))
  (h3 : (((x ^ (2 : ℕ)) - x) + (1 /. 20)) > 0)
  (h4 : (((x ^ (2 : ℕ)) - x) - (1 /. 20)) < 0)
  (h5 : (((5 + (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x) ∨ (x < ((5 - (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10)))
  (h6 : ((5 - (Real.rpow (30 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x)
  (h7 : x < ((5 + (Real.rpow (30 : ℝ) (((2 : ℝ))⁻¹))) /. 10))
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((((5 - (Real.rpow (30 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x_1) ∧ (x_1 < ((5 - (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10))) ∨ ((((5 + (Real.rpow (20 : ℝ) (((2 : ℝ))⁻¹))) /. 10) < x_1) ∧ (x_1 < ((5 + (Real.rpow (30 : ℝ) (((2 : ℝ))⁻¹))) /. 10))))})) ↔ (|((x * (1 - x)))| < (((005 : ℝ) /. (100 : ℝ)))) := by
  sorry
