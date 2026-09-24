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

-- exercise: exercise_1675

theorem proof_gap_exercise_1675_1
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  : ((fun (x_1 : ℝ) => ((x_1 ^ (2 : ℕ)) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (((3 : ℝ))⁻¹)))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = ((fun (x_1 : ℝ) => ((1 /. 3) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)))) • (fderiv ℝ (fun (x_1 : ℝ) => (1 + (x_1 ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1675_2
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((fun (x_1 : ℝ) => ((x_1 ^ (2 : ℕ)) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (((3 : ℝ))⁻¹)))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = ((fun (x_1 : ℝ) => ((1 /. 3) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)))) • (fderiv ℝ (fun (x_1 : ℝ) => (1 + (x_1 ^ (3 : ℕ)))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (2 : ℕ)) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (((3 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)) * (iteratedDeriv 1 (fun t => (1 + (t ^ (3 : ℕ)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 3) * (F_3 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1675_3
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((fun (x_1 : ℝ) => ((x_1 ^ (2 : ℕ)) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (((3 : ℝ))⁻¹)))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = ((fun (x_1 : ℝ) => ((1 /. 3) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)))) • (fderiv ℝ (fun (x_1 : ℝ) => (1 + (x_1 ^ (3 : ℕ)))))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (2 : ℕ)) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (((3 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)) * (iteratedDeriv 1 (fun t => (1 + (t ^ (3 : ℕ)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 3) * (F_3 x_1)))))))}))
  : ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)) * (iteratedDeriv 1 (fun t => (1 + (t ^ (3 : ℕ)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 3) * (F_3 x_1)))))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_5 x_1) = (((1 /. 4) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (4 /. 3))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1675_4
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((fun (x_1 : ℝ) => ((x_1 ^ (2 : ℕ)) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (((3 : ℝ))⁻¹)))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = ((fun (x_1 : ℝ) => ((1 /. 3) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)))) • (fderiv ℝ (fun (x_1 : ℝ) => (1 + (x_1 ^ (3 : ℕ)))))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (2 : ℕ)) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (((3 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)) * (iteratedDeriv 1 (fun t => (1 + (t ^ (3 : ℕ)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 3) * (F_3 x_1)))))))}))
  (h5 : ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.rpow (1 + (x_1 ^ (3 : ℕ))) (1 /. 3)) * (iteratedDeriv 1 (fun t => (1 + (t ^ (3 : ℕ)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 3) * (F_3 x_1)))))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_5 x_1) = (((1 /. 4) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (4 /. 3))) + C_1))))))}))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (2 : ℕ)) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (((3 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_5 x_1) = (((1 /. 4) * (Real.rpow (1 + (x_1 ^ (3 : ℕ))) (4 /. 3))) + C_1))))))}) := by
  sorry
