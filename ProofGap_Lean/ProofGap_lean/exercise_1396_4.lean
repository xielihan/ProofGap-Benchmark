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

-- exercise: exercise_1396_4

theorem proof_gap_exercise_1396_4_1
  (h1 : v_uCE_u94 = |(((Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) - (((164872 : ℝ) /. (100000 : ℝ)))))|)
  : (Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) = (Real.exp (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_1396_4_2
  (h1 : v_uCE_u94 = |(((Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) - (((164872 : ℝ) /. (100000 : ℝ)))))|)
  (h2 : (Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) = (Real.exp (1 /. 2)))
  : |((Real.exp (1 /. 2)) - (∑ n ∈ Finset.Icc (0 : ℕ) (6 : ℕ), ((1 /. (n)!) * ((1 /. 2) ^ n))))| ≤ (∑' n, if (7 : ℕ) ≤ n then ((1 /. (n)!) * ((1 /. 2) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_1396_4_3
  (h1 : v_uCE_u94 = |(((Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) - (((164872 : ℝ) /. (100000 : ℝ)))))|)
  (h2 : (Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) = (Real.exp (1 /. 2)))
  (h3 : |((Real.exp (1 /. 2)) - (∑ n ∈ Finset.Icc (0 : ℕ) (6 : ℕ), ((1 /. (n)!) * ((1 /. 2) ^ n))))| ≤ (∑' n, if (7 : ℕ) ≤ n then ((1 /. (n)!) * ((1 /. 2) ^ n)) else 0))
  : (∑' n, if (7 : ℕ) ≤ n then ((1 /. (n)!) * ((1 /. 2) ^ n)) else 0) < (((1 /. ((7 : ℕ))!) * ((1 /. 2) ^ (7 : ℕ))) * (1 /. (1 - ((1 /. 8) * (1 /. 2))))) := by
  sorry

theorem proof_gap_exercise_1396_4_4
  (h1 : v_uCE_u94 = |(((Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) - (((164872 : ℝ) /. (100000 : ℝ)))))|)
  (h2 : (Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) = (Real.exp (1 /. 2)))
  (h3 : |((Real.exp (1 /. 2)) - (∑ n ∈ Finset.Icc (0 : ℕ) (6 : ℕ), ((1 /. (n)!) * ((1 /. 2) ^ n))))| ≤ (∑' n, if (7 : ℕ) ≤ n then ((1 /. (n)!) * ((1 /. 2) ^ n)) else 0))
  (h4 : (∑' n, if (7 : ℕ) ≤ n then ((1 /. (n)!) * ((1 /. 2) ^ n)) else 0) < (((1 /. ((7 : ℕ))!) * ((1 /. 2) ^ (7 : ℕ))) * (1 /. (1 - ((1 /. 8) * (1 /. 2))))))
  : |((Real.rpow (Real.exp 1) (((2 : ℝ))⁻¹)) - (((164872 : ℝ) /. (100000 : ℝ))))| ≤ ((((17 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))) := by
  sorry
