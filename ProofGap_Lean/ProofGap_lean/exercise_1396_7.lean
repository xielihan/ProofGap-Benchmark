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

-- exercise: exercise_1396_7

theorem proof_gap_exercise_1396_7_1
  : (((08 : ℝ) /. (10 : ℝ))) ∈ (Set.Ioo (-(1 : ℝ)) 1) := by
  sorry

theorem proof_gap_exercise_1396_7_2
  (h1 : (((08 : ℝ) /. (10 : ℝ))) ∈ (Set.Ioo (-(1 : ℝ)) 1))
  : |((Real.arctan (((08 : ℝ) /. (10 : ℝ)))) - (∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))))| ≤ ((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ))) := by
  sorry

theorem proof_gap_exercise_1396_7_3
  (h1 : (((08 : ℝ) /. (10 : ℝ))) ∈ (Set.Ioo (-(1 : ℝ)) 1))
  (h2 : |((Real.arctan (((08 : ℝ) /. (10 : ℝ)))) - (∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))))| ≤ ((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ))))
  : |((∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))) - (((067474 : ℝ) /. (100000 : ℝ))))| ≤ ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))) := by
  sorry

theorem proof_gap_exercise_1396_7_4
  (h1 : (((08 : ℝ) /. (10 : ℝ))) ∈ (Set.Ioo (-(1 : ℝ)) 1))
  (h2 : |((Real.arctan (((08 : ℝ) /. (10 : ℝ)))) - (∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))))| ≤ ((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ))))
  (h3 : |((∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))) - (((067474 : ℝ) /. (100000 : ℝ))))| ≤ ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))))
  : (exists (v_uCE_u94 : ℝ), (((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 ≥ 0)) ∧ (v_uCE_u94 < ((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1396_7_5
  (h1 : (((08 : ℝ) /. (10 : ℝ))) ∈ (Set.Ioo (-(1 : ℝ)) 1))
  (h2 : |((Real.arctan (((08 : ℝ) /. (10 : ℝ)))) - (∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))))| ≤ ((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ))))
  (h3 : |((∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))) - (((067474 : ℝ) /. (100000 : ℝ))))| ≤ ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))))
  (h4 : (exists (v_uCE_u94 : ℝ), (((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 ≥ 0)) ∧ (v_uCE_u94 < ((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ)))))))
  : |(((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ))) - ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))))| ≤ ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))) := by
  sorry

theorem proof_gap_exercise_1396_7_6
  (h1 : (((08 : ℝ) /. (10 : ℝ))) ∈ (Set.Ioo (-(1 : ℝ)) 1))
  (h2 : |((Real.arctan (((08 : ℝ) /. (10 : ℝ)))) - (∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))))| ≤ ((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ))))
  (h3 : |((∑ k ∈ Finset.Icc (0 : ℕ) (19 : ℕ), (((-(1 : ℤ)) ^ k) * (((((08 : ℝ) /. (10 : ℝ))) ^ ((2 * k) + 1)) /. ((2 * k) + 1)))) - (((067474 : ℝ) /. (100000 : ℝ))))| ≤ ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))))
  (h4 : (exists (v_uCE_u94 : ℝ), (((v_uCE_u94 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94 ≥ 0)) ∧ (v_uCE_u94 < ((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ)))))))
  (h5 : |(((1 /. 41) * ((((08 : ℝ) /. (10 : ℝ))) ^ (41 : ℕ))) - ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))))| ≤ ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))))
  : |((Real.arctan (((08 : ℝ) /. (10 : ℝ)))) - (((067474 : ℝ) /. (100000 : ℝ))))| ≤ ((((26 : ℝ) /. (10 : ℝ))) * ((10 : ℝ) ^ (-(6 : ℤ)))) := by
  sorry
