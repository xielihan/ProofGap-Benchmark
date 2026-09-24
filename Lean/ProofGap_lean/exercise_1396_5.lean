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

-- exercise: exercise_1396_5

theorem proof_gap_exercise_1396_5_1
  : |((Real.sin (Real.pi /. 10)) - (((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))))| ≤ ((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ))) := by
  sorry

theorem proof_gap_exercise_1396_5_2
  (h1 : |((Real.sin (Real.pi /. 10)) - (((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))))| ≤ ((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ))))
  : |((((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))) - (((0309017 : ℝ) /. (1000000 : ℝ))))| ≤ (6 * ((10 : ℝ) ^ (-(8 : ℤ)))) := by
  sorry

theorem proof_gap_exercise_1396_5_3
  (h1 : |((Real.sin (Real.pi /. 10)) - (((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))))| ≤ ((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ))))
  (h2 : |((((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))) - (((0309017 : ℝ) /. (1000000 : ℝ))))| ≤ (6 * ((10 : ℝ) ^ (-(8 : ℤ)))))
  : (exists (v_uCE_u94 : ℝ), (((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 ≥ 0)) ∧ (v_uCE_u94 < ((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1396_5_4
  (h1 : |((Real.sin (Real.pi /. 10)) - (((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))))| ≤ ((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ))))
  (h2 : |((((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))) - (((0309017 : ℝ) /. (1000000 : ℝ))))| ≤ (6 * ((10 : ℝ) ^ (-(8 : ℤ)))))
  (h3 : (exists (v_uCE_u94 : ℝ), (((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 ≥ 0)) ∧ (v_uCE_u94 < ((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ)))))))
  : |(((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ))) - (6 * ((10 : ℝ) ^ (-(8 : ℤ)))))| ≤ (6 * ((10 : ℝ) ^ (-(8 : ℤ)))) := by
  sorry

theorem proof_gap_exercise_1396_5_5
  (h1 : |((Real.sin (Real.pi /. 10)) - (((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))))| ≤ ((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ))))
  (h2 : |((((Real.pi /. 10) - ((1 /. ((3 : ℕ))!) * ((Real.pi /. 10) ^ (3 : ℕ)))) + ((1 /. ((5 : ℕ))!) * ((Real.pi /. 10) ^ (5 : ℕ)))) - (((0309017 : ℝ) /. (1000000 : ℝ))))| ≤ (6 * ((10 : ℝ) ^ (-(8 : ℤ)))))
  (h3 : (exists (v_uCE_u94 : ℝ), (((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 ≥ 0)) ∧ (v_uCE_u94 < ((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ)))))))
  (h4 : |(((1 /. ((7 : ℕ))!) * ((Real.pi /. 10) ^ (7 : ℕ))) - (6 * ((10 : ℝ) ^ (-(8 : ℤ)))))| ≤ (6 * ((10 : ℝ) ^ (-(8 : ℤ)))))
  : |((Real.sin (Real.pi /. 10)) - (((0309017 : ℝ) /. (1000000 : ℝ))))| ≤ (6 * ((10 : ℝ) ^ (-(8 : ℤ)))) := by
  sorry
