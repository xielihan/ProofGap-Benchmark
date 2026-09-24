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

-- exercise: exercise_1851

theorem proof_gap_exercise_1851_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ∈ (Set.Ioo ((1 - (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2) ((1 + (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2))))) := by
  sorry

theorem proof_gap_exercise_1851_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ∈ (Set.Ioo ((1 - (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2) ((1 + (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x /. (Real.rpow ((5 + x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((x - (1 /. 2)) + (1 /. 2)) /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) := by
  sorry

theorem proof_gap_exercise_1851_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ∈ (Set.Ioo ((1 - (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2) ((1 + (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2))))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x /. (Real.rpow ((5 + x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((x - (1 /. 2)) + (1 /. 2)) /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((x - (1 /. 2)) + (1 /. 2)) /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)) (F_7 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => ((21 /. 4) - ((t - (1 /. 2)) ^ (2 : ℕ)))) x))) ∧ ((iteratedDeriv 1 (fun t => F_7 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => (t - (1 /. 2))) x)))) ∧ ((F_9 x) = (((-(1 /. 2)) * (F_5 x)) + ((1 /. 2) * (F_7 x)))))))))}) := by
  sorry

theorem proof_gap_exercise_1851_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ∈ (Set.Ioo ((1 - (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2) ((1 + (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2))))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x /. (Real.rpow ((5 + x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((x - (1 /. 2)) + (1 /. 2)) /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((x - (1 /. 2)) + (1 /. 2)) /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)) (F_7 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => ((21 /. 4) - ((t - (1 /. 2)) ^ (2 : ℕ)))) x))) ∧ ((iteratedDeriv 1 (fun t => F_7 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => (t - (1 /. 2))) x)))) ∧ ((F_9 x) = (((-(1 /. 2)) * (F_5 x)) + ((1 /. 2) * (F_7 x)))))))))}))
  : ({F_14 : (ℝ -> ℝ) | (exists (F_10 : (ℝ -> ℝ)) (F_12 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_10 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => ((21 /. 4) - ((t - (1 /. 2)) ^ (2 : ℕ)))) x))) ∧ ((iteratedDeriv 1 (fun t => F_12 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => (t - (1 /. 2))) x)))) ∧ ((F_14 x) = (((-(1 /. 2)) * (F_10 x)) + ((1 /. 2) * (F_12 x)))))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_15 x) = (((-(Real.rpow ((5 + x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) + ((1 /. 2) * (Real.arcsin (((2 * x) - 1) /. (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹)))))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1851_5
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ∈ (Set.Ioo ((1 - (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2) ((1 + (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹))) /. 2))))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x /. (Real.rpow ((5 + x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((x - (1 /. 2)) + (1 /. 2)) /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((x - (1 /. 2)) + (1 /. 2)) /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)) (F_7 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => ((21 /. 4) - ((t - (1 /. 2)) ^ (2 : ℕ)))) x))) ∧ ((iteratedDeriv 1 (fun t => F_7 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => (t - (1 /. 2))) x)))) ∧ ((F_9 x) = (((-(1 /. 2)) * (F_5 x)) + ((1 /. 2) * (F_7 x)))))))))}))
  (h5 : ({F_14 : (ℝ -> ℝ) | (exists (F_10 : (ℝ -> ℝ)) (F_12 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_10 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => ((21 /. 4) - ((t - (1 /. 2)) ^ (2 : ℕ)))) x))) ∧ ((iteratedDeriv 1 (fun t => F_12 t) x) = ((1 /. (Real.rpow ((21 /. 4) - ((x - (1 /. 2)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => (t - (1 /. 2))) x)))) ∧ ((F_14 x) = (((-(1 /. 2)) * (F_10 x)) + ((1 /. 2) * (F_12 x)))))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_15 x) = (((-(Real.rpow ((5 + x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) + ((1 /. 2) * (Real.arcsin (((2 * x) - 1) /. (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹)))))) + C_1))))))}))
  : ({F_16 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_16 t) x) = ((x /. (Real.rpow ((5 + x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_17 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_17 x) = (((-(Real.rpow ((5 + x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) + ((1 /. 2) * (Real.arcsin (((2 * x) - 1) /. (Real.rpow (21 : ℝ) (((2 : ℝ))⁻¹)))))) + C_1))))))}) := by
  sorry
