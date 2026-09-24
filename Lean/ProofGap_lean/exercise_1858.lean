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

-- exercise: exercise_1858

theorem proof_gap_exercise_1858_1
  (C : ℝ)
  (C_1 : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : C_1 ∈ (Set.univ : Set ℝ))
  (h3 : y = (x + 1))
  : y ≠ 0 := by
  sorry

theorem proof_gap_exercise_1858_2
  (C : ℝ)
  (C_1 : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : C_1 ∈ (Set.univ : Set ℝ))
  (h3 : y = (x + 1))
  (h4 : y ≠ 0)
  : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. ((x + 1) * (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) y) = ((iteratedDeriv 1 (fun t => t) y) /. (y * (Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)))))))})))) := by
  sorry

theorem proof_gap_exercise_1858_3
  (C : ℝ)
  (C_1 : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : C_1 ∈ (Set.univ : Set ℝ))
  (h3 : y = (x + 1))
  (h4 : y ≠ 0)
  (h5 : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. ((x + 1) * (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) y) = ((iteratedDeriv 1 (fun t => t) y) /. (y * (Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)))))))})))))
  : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_4 : (ℝ -> ℝ) | (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) y) = ((iteratedDeriv 1 (fun t => t) y) /. (y * (Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)))))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) y) = ((iteratedDeriv 1 (fun t => (1 /. t)) y) /. (Real.rpow (((2 /. (y ^ (2 : ℕ))) - (2 /. y)) + 1) (((2 : ℝ))⁻¹)))) ∧ ((F_6 y) = (-(F_5 y)))))))})))) := by
  sorry

theorem proof_gap_exercise_1858_4
  (C : ℝ)
  (C_1 : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : C_1 ∈ (Set.univ : Set ℝ))
  (h3 : y = (x + 1))
  (h4 : y ≠ 0)
  (h5 : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. ((x + 1) * (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) y) = ((iteratedDeriv 1 (fun t => t) y) /. (y * (Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)))))))})))))
  (h6 : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_4 : (ℝ -> ℝ) | (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) y) = ((iteratedDeriv 1 (fun t => t) y) /. (y * (Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)))))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) y) = ((iteratedDeriv 1 (fun t => (1 /. t)) y) /. (Real.rpow (((2 /. (y ^ (2 : ℕ))) - (2 /. y)) + 1) (((2 : ℝ))⁻¹)))) ∧ ((F_6 y) = (-(F_5 y)))))))})))))
  : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = ((1 /. ((x + 1) * (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (C_1_1 : ℝ), ((C_1_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (exists (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y = (x + 1))) ∧ ((F_8 x) = (((-(1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.log |((((1 /. y) - (1 /. 2)) + ((Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)) /. (y * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))))|)) + C_1_1))))))))})))) := by
  sorry

theorem proof_gap_exercise_1858_5
  (C : ℝ)
  (C_1 : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : C_1 ∈ (Set.univ : Set ℝ))
  (h3 : y = (x + 1))
  (h4 : y ≠ 0)
  (h5 : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. ((x + 1) * (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) y) = ((iteratedDeriv 1 (fun t => t) y) /. (y * (Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)))))))})))))
  (h6 : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_4 : (ℝ -> ℝ) | (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) y) = ((iteratedDeriv 1 (fun t => t) y) /. (y * (Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)))))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) y) = ((iteratedDeriv 1 (fun t => (1 /. t)) y) /. (Real.rpow (((2 /. (y ^ (2 : ℕ))) - (2 /. y)) + 1) (((2 : ℝ))⁻¹)))) ∧ ((F_6 y) = (-(F_5 y)))))))})))))
  (h7 : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = ((1 /. ((x + 1) * (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (C_1_1 : ℝ), ((C_1_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (exists (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y = (x + 1))) ∧ ((F_8 x) = (((-(1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.log |((((1 /. y) - (1 /. 2)) + ((Real.rpow (((y ^ (2 : ℕ)) - (2 * y)) + 2) (((2 : ℝ))⁻¹)) /. (y * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))))|)) + C_1_1))))))))})))))
  : (x ∈ (Set.univ : Set ℝ)) → ((x ≠ (-(1 : ℝ))) → (((x + 1) > 0) → (({F_9 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_9 t) x) = ((1 /. ((x + 1) * (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_10 : (ℝ -> ℝ) | (exists (C_2 : ℝ), ((C_2 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_10 x) = (((-(1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.log |((((1 - x) + (Real.rpow (2 * ((x ^ (2 : ℕ)) + 1)) (((2 : ℝ))⁻¹))) /. (x + 1)))|)) + C_2))))))})))) := by
  sorry
