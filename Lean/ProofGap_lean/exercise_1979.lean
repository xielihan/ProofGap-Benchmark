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

-- exercise: exercise_1979

theorem proof_gap_exercise_1979_1
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((1 /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_5 x_1) = ((F_3 x_1) + (F_4 x_1))))))))}) := by
  sorry

theorem proof_gap_exercise_1979_2
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((1 /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_5 x_1) = ((F_3 x_1) + (F_4 x_1))))))))}))
  : ({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) + (1 /. 2))) x_1) /. (Real.rpow ((((x_1 ^ (2 : ℕ)) + (1 /. 2)) ^ (2 : ℕ)) + (3 /. 4)) (((2 : ℝ))⁻¹)))) ∧ ((F_8 x_1) = ((1 /. 2) * (F_7 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1979_3
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((1 /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_5 x_1) = ((F_3 x_1) + (F_4 x_1))))))))}))
  (h3 : ({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) + (1 /. 2))) x_1) /. (Real.rpow ((((x_1 ^ (2 : ℕ)) + (1 /. 2)) ^ (2 : ℕ)) + (3 /. 4)) (((2 : ℝ))⁻¹)))) ∧ ((F_8 x_1) = ((1 /. 2) * (F_7 x_1)))))))}))
  : ({F_9 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_9 t) x_1) = ((1 /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_10 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → (((iteratedDeriv 1 (fun t => F_10 t) x_1) = ((iteratedDeriv 1 (fun t => (1 /. (t ^ (2 : ℕ)))) x_1) /. (Real.rpow ((((1 /. (x_1 ^ (2 : ℕ))) + (1 /. 2)) ^ (2 : ℕ)) + (3 /. 4)) (((2 : ℝ))⁻¹)))) ∧ ((F_11 x_1) = ((-(1 /. 2)) * (F_10 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1979_4
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((1 /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_5 x_1) = ((F_3 x_1) + (F_4 x_1))))))))}))
  (h3 : ({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) + (1 /. 2))) x_1) /. (Real.rpow ((((x_1 ^ (2 : ℕ)) + (1 /. 2)) ^ (2 : ℕ)) + (3 /. 4)) (((2 : ℝ))⁻¹)))) ∧ ((F_8 x_1) = ((1 /. 2) * (F_7 x_1)))))))}))
  (h4 : ({F_9 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_9 t) x_1) = ((1 /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_10 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → (((iteratedDeriv 1 (fun t => F_10 t) x_1) = ((iteratedDeriv 1 (fun t => (1 /. (t ^ (2 : ℕ)))) x_1) /. (Real.rpow ((((1 /. (x_1 ^ (2 : ℕ))) + (1 /. 2)) ^ (2 : ℕ)) + (3 /. 4)) (((2 : ℝ))⁻¹)))) ∧ ((F_11 x_1) = ((-(1 /. 2)) * (F_10 x_1)))))))}))
  : ({F_12 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_12 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_13 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((F_13 x_1) = (((1 /. 2) * (Real.log ((((x_1 ^ (2 : ℕ)) + (1 /. 2)) + (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) /. (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. 2)) + (Real.rpow ((((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) /. (x_1 ^ (4 : ℕ))) (((2 : ℝ))⁻¹)))))) + C))))))}) := by
  sorry

theorem proof_gap_exercise_1979_5
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((1 /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_5 x_1) = ((F_3 x_1) + (F_4 x_1))))))))}))
  (h3 : ({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = ((x_1 /. (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) + (1 /. 2))) x_1) /. (Real.rpow ((((x_1 ^ (2 : ℕ)) + (1 /. 2)) ^ (2 : ℕ)) + (3 /. 4)) (((2 : ℝ))⁻¹)))) ∧ ((F_8 x_1) = ((1 /. 2) * (F_7 x_1)))))))}))
  (h4 : ({F_9 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_9 t) x_1) = ((1 /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_10 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → (((iteratedDeriv 1 (fun t => F_10 t) x_1) = ((iteratedDeriv 1 (fun t => (1 /. (t ^ (2 : ℕ)))) x_1) /. (Real.rpow ((((1 /. (x_1 ^ (2 : ℕ))) + (1 /. 2)) ^ (2 : ℕ)) + (3 /. 4)) (((2 : ℝ))⁻¹)))) ∧ ((F_11 x_1) = ((-(1 /. 2)) * (F_10 x_1)))))))}))
  (h5 : ({F_12 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_12 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_13 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((F_13 x_1) = (((1 /. 2) * (Real.log ((((x_1 ^ (2 : ℕ)) + (1 /. 2)) + (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))) /. (((1 /. (x_1 ^ (2 : ℕ))) + (1 /. 2)) + (Real.rpow ((((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) /. (x_1 ^ (4 : ℕ))) (((2 : ℝ))⁻¹)))))) + C))))))}))
  : ({F_14 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((iteratedDeriv 1 (fun t => F_14 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (x_1 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) → ((F_15 x_1) = (((1 /. 2) * (Real.log (((x_1 ^ (2 : ℕ)) * ((1 + (2 * (x_1 ^ (2 : ℕ)))) + (2 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))))) /. ((2 + (x_1 ^ (2 : ℕ))) + (2 * (Real.rpow (((x_1 ^ (4 : ℕ)) + (x_1 ^ (2 : ℕ))) + 1) (((2 : ℝ))⁻¹))))))) + C))))))}) := by
  sorry
