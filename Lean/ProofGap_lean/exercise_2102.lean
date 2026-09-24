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

-- exercise: exercise_2102

theorem proof_gap_exercise_2102_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((x /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - (2 * (F_3 x))))))))}) := by
  sorry

theorem proof_gap_exercise_2102_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((x /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - (2 * (F_3 x))))))))}))
  : ({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_8 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) x))) ∧ ((F_11 x) = ((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - (2 * (F_8 x))))))))}) := by
  sorry

theorem proof_gap_exercise_2102_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((x /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - (2 * (F_3 x))))))))}))
  (h4 : ({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_8 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) x))) ∧ ((F_11 x) = ((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - (2 * (F_8 x))))))))}))
  : ({F_12 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_12 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_16 : (ℝ -> ℝ) | (exists (F_13 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_13 t) x) = (iteratedDeriv 1 (fun t => t) x)) ∧ ((F_16 x) = (((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - ((2 * (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) + (2 * (F_13 x))))))))}) := by
  sorry

theorem proof_gap_exercise_2102_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((x /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - (2 * (F_3 x))))))))}))
  (h4 : ({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_8 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) x))) ∧ ((F_11 x) = ((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - (2 * (F_8 x))))))))}))
  (h5 : ({F_12 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_12 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_16 : (ℝ -> ℝ) | (exists (F_13 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_13 t) x) = (iteratedDeriv 1 (fun t => t) x)) ∧ ((F_16 x) = (((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - ((2 * (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) + (2 * (F_13 x))))))))}))
  : ({F_17 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_17 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_18 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_18 x) = ((((x * ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ^ (2 : ℕ))) - ((2 * (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) + (2 * x)) + C_1))))))}) := by
  sorry
