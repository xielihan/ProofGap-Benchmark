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

-- exercise: exercise_1636

theorem proof_gap_exercise_1636_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x > 0)
  : ((1 - (1 /. (x ^ (2 : ℕ)))) * (Real.rpow (x * (Real.rpow x (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) = ((Real.rpow x (3 /. 4)) - (Real.rpow x (-(5 /. 4)))) := by
  sorry

theorem proof_gap_exercise_1636_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x > 0)
  (h3 : ((1 - (1 /. (x ^ (2 : ℕ)))) * (Real.rpow (x * (Real.rpow x (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) = ((Real.rpow x (3 /. 4)) - (Real.rpow x (-(5 /. 4)))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((1 - (1 /. (x_1 ^ (2 : ℕ)))) * (Real.rpow (x_1 * (Real.rpow x_1 (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.rpow x_1 (3 /. 4)) - (Real.rpow x_1 (-(5 /. 4)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_1636_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x > 0)
  (h3 : ((1 - (1 /. (x ^ (2 : ℕ)))) * (Real.rpow (x * (Real.rpow x (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) = ((Real.rpow x (3 /. 4)) - (Real.rpow x (-(5 /. 4)))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((1 - (1 /. (x_1 ^ (2 : ℕ)))) * (Real.rpow (x_1 * (Real.rpow x_1 (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.rpow x_1 (3 /. 4)) - (Real.rpow x_1 (-(5 /. 4)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((1 - (1 /. (x_1 ^ (2 : ℕ)))) * (Real.rpow (x_1 * (Real.rpow x_1 (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((F_5 x_1) = ((((4 /. 7) * (Real.rpow x_1 (7 /. 4))) + (4 * (Real.rpow x_1 (-(1 /. 4))))) + C_1))))))})))) := by
  sorry

theorem proof_gap_exercise_1636_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x > 0)
  (h3 : ((1 - (1 /. (x ^ (2 : ℕ)))) * (Real.rpow (x * (Real.rpow x (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) = ((Real.rpow x (3 /. 4)) - (Real.rpow x (-(5 /. 4)))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((1 - (1 /. (x_1 ^ (2 : ℕ)))) * (Real.rpow (x_1 * (Real.rpow x_1 (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.rpow x_1 (3 /. 4)) - (Real.rpow x_1 (-(5 /. 4)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h5 : (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((1 - (1 /. (x_1 ^ (2 : ℕ)))) * (Real.rpow (x_1 * (Real.rpow x_1 (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((F_5 x_1) = ((((4 /. 7) * (Real.rpow x_1 (7 /. 4))) + (4 * (Real.rpow x_1 (-(1 /. 4))))) + C_1))))))})))))
  : (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = (((1 - (1 /. (x_1 ^ (2 : ℕ)))) * (Real.rpow (x_1 * (Real.rpow x_1 (((2 : ℝ))⁻¹))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((F_7 x_1) = (((4 * ((x_1 ^ (2 : ℕ)) + 7)) /. (7 * (Real.rpow x_1 (((4 : ℝ))⁻¹)))) + C_1))))))})))) := by
  sorry
