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

-- exercise: exercise_1396_3

theorem proof_gap_exercise_1396_3_1
  (h1 : v_uCE_u94 = |(((Real.rpow (4000 : ℝ) (((12 : ℝ))⁻¹)) - (((19960 : ℝ) /. (10000 : ℝ)))))|)
  : (Real.rpow (4000 : ℝ) (((12 : ℝ))⁻¹)) = (2 * (Real.rpow (1 - (3 /. 128)) (1 /. 12))) := by
  sorry

theorem proof_gap_exercise_1396_3_2
  (h1 : v_uCE_u94 = |(((Real.rpow (4000 : ℝ) (((12 : ℝ))⁻¹)) - (((19960 : ℝ) /. (10000 : ℝ)))))|)
  (h2 : (Real.rpow (4000 : ℝ) (((12 : ℝ))⁻¹)) = (2 * (Real.rpow (1 - (3 /. 128)) (1 /. 12))))
  : |((Real.rpow (1 - (3 /. 128)) (1 /. 12)) - (1 - ((1 /. 12) * (3 /. 128))))| ≤ (((3 /. 128) ^ (2 : ℕ)) * (1 /. (1 - (3 /. 128)))) := by
  sorry

theorem proof_gap_exercise_1396_3_3
  (h1 : v_uCE_u94 = |(((Real.rpow (4000 : ℝ) (((12 : ℝ))⁻¹)) - (((19960 : ℝ) /. (10000 : ℝ)))))|)
  (h2 : (Real.rpow (4000 : ℝ) (((12 : ℝ))⁻¹)) = (2 * (Real.rpow (1 - (3 /. 128)) (1 /. 12))))
  (h3 : |((Real.rpow (1 - (3 /. 128)) (1 /. 12)) - (1 - ((1 /. 12) * (3 /. 128))))| ≤ (((3 /. 128) ^ (2 : ℕ)) * (1 /. (1 - (3 /. 128)))))
  : |((Real.rpow (4000 : ℝ) (((12 : ℝ))⁻¹)) - (((19960 : ℝ) /. (10000 : ℝ))))| ≤ ((((5625 : ℝ) /. (1000 : ℝ))) * ((10 : ℝ) ^ (-(4 : ℤ)))) := by
  sorry
