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

-- exercise: exercise_1664

theorem proof_gap_exercise_1664_1
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((3 * (x ^ (2 : ℕ))) - 2) > 0)
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((1 /. (Real.rpow ((3 * (x_1 ^ (2 : ℕ))) - 2) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((1 /. (Real.rpow ((((Real.rpow (3 /. 2) (((2 : ℝ))⁻¹)) * x_1) ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (F_3 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1664_2
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((3 * (x ^ (2 : ℕ))) - 2) > 0)
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((1 /. (Real.rpow ((3 * (x_1 ^ (2 : ℕ))) - 2) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((1 /. (Real.rpow ((((Real.rpow (3 /. 2) (((2 : ℝ))⁻¹)) * x_1) ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (F_3 x_1)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((1 /. (Real.rpow ((((Real.rpow (3 /. 2) (((2 : ℝ))⁻¹)) * x_1) ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (F_5 x_1)))))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → ((F_7 x_1) = ((((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹))) * (Real.log |(((x_1 * (Real.rpow (3 /. 2) (((2 : ℝ))⁻¹))) + (Real.rpow (((3 /. 2) * (x_1 ^ (2 : ℕ))) - 1) (((2 : ℝ))⁻¹))))|)) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1664_3
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((3 * (x ^ (2 : ℕ))) - 2) > 0)
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((1 /. (Real.rpow ((3 * (x_1 ^ (2 : ℕ))) - 2) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((1 /. (Real.rpow ((((Real.rpow (3 /. 2) (((2 : ℝ))⁻¹)) * x_1) ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (F_3 x_1)))))))}))
  (h5 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((1 /. (Real.rpow ((((Real.rpow (3 /. 2) (((2 : ℝ))⁻¹)) * x_1) ^ (2 : ℕ)) - 1) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (F_5 x_1)))))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → ((F_7 x_1) = ((((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹))) * (Real.log |(((x_1 * (Real.rpow (3 /. 2) (((2 : ℝ))⁻¹))) + (Real.rpow (((3 /. 2) * (x_1 ^ (2 : ℕ))) - 1) (((2 : ℝ))⁻¹))))|)) + C_1))))))}))
  : ({F_8 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → ((iteratedDeriv 1 (fun t => F_8 t) x_1) = ((1 /. (Real.rpow ((3 * (x_1 ^ (2 : ℕ))) - 2) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (((3 * (x_1 ^ (2 : ℕ))) - 2) > 0)) → ((F_9 x_1) = (((1 /. (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹))) * (Real.log |(((x_1 * (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹))) + (Real.rpow ((3 * (x_1 ^ (2 : ℕ))) - 2) (((2 : ℝ))⁻¹))))|)) + C_1))))))}) := by
  sorry
