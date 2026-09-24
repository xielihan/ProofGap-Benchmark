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

-- exercise: exercise_3767

theorem proof_gap_exercise_3767_1
  (I : (ℝ -> ℝ))
  (h1 : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  : (forall (x : ℝ) (n : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ x)) ∧ (x < 1)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((0 ≤ ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) < (1 /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_3767_2
  (I : (ℝ -> ℝ))
  (h1 : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  (h2 : (forall (x : ℝ) (n : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ x)) ∧ (x < 1)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((0 ≤ ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) < (1 /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3767_3
  (I : (ℝ -> ℝ))
  (h1 : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  (h2 : (forall (x : ℝ) (n : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ x)) ∧ (x < 1)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((0 ≤ ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) < (1 /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))))
  : ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))) = (Real.pi /. 2) := by
  sorry

theorem proof_gap_exercise_3767_4
  (I : (ℝ -> ℝ))
  (h1 : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  (h2 : (forall (x : ℝ) (n : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ x)) ∧ (x < 1)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((0 ≤ ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) < (1 /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))))
  (h4 : ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))) = (Real.pi /. 2))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi /. 2) := by
  sorry

theorem proof_gap_exercise_3767_5
  (I : (ℝ -> ℝ))
  (h1 : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  (h2 : (forall (x : ℝ) (n : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ x)) ∧ (x < 1)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((0 ≤ ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) < (1 /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))))
  (h4 : ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))) = (Real.pi /. 2))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi /. 2))
  : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → (TendstoUniformlyOn (fun (_ : ℕ) (n : ℝ) => I n) (fun n => ∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) Filter.atTop ({x_1 : ℝ | 0 <= x_1})))) := by
  sorry

theorem proof_gap_exercise_3767_6
  (I : (ℝ -> ℝ))
  (h1 : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  (h2 : (forall (x : ℝ) (n : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ x)) ∧ (x < 1)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((0 ≤ ((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) < (1 /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))))))
  (h3 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))))
  (h4 : ((Real.arcsin (1 : ℝ)) - (Real.arcsin (0 : ℝ))) = (Real.pi /. 2))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi /. 2))
  (h6 : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → (TendstoUniformlyOn (fun (_ : ℕ) (n : ℝ) => I n) (fun n => ∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) Filter.atTop ({x_1 : ℝ | 0 <= x_1})))))
  : (forall (n : ℝ), (((n ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({x_1 : ℝ | 0 <= x_1}))) → (TendstoUniformlyOn (fun (_ : ℕ) (n : ℝ) => I n) (fun n => ∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x n) /. (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) Filter.atTop ({x_1 : ℝ | 0 <= x_1})))) := by
  sorry
