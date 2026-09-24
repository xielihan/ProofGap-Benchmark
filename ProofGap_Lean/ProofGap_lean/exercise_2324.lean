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

-- exercise: exercise_2324

theorem proof_gap_exercise_2324_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((x ^ (9 : ℕ)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) ≤ ((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) ∧ (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) ≤ (x ^ (9 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_2324_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((x ^ (9 : ℕ)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) ≤ ((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) ∧ (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) ≤ (x ^ (9 : ℕ)))))))
  : ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ)))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2324_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((x ^ (9 : ℕ)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) ≤ ((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) ∧ (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) ≤ (x ^ (9 : ℕ)))))))
  (h2 : ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ)))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2324_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((x ^ (9 : ℕ)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) ≤ ((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) ∧ (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) ≤ (x ^ (9 : ℕ)))))))
  (h2 : ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ)))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ))) = (1 /. 10) := by
  sorry

theorem proof_gap_exercise_2324_5
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((x ^ (9 : ℕ)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) ≤ ((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) ∧ (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) ≤ (x ^ (9 : ℕ)))))))
  (h2 : ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ)))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ))) = (1 /. 10))
  : (1 /. (10 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2324_6
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((((x ^ (9 : ℕ)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) ≤ ((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹)))) ∧ (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) ≤ (x ^ (9 : ℕ)))))))
  (h2 : ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ)))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ (9 : ℕ)) * (1 : ℝ))) = (1 /. 10))
  (h5 : (1 /. (10 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) ≤ (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (9 : ℕ)) /. (Real.rpow (1 + x) (((2 : ℝ))⁻¹))) * (1 : ℝ))) ≤ (1 /. 10) := by
  sorry
