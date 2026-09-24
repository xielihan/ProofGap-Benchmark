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

-- exercise: exercise_1842

theorem proof_gap_exercise_1842_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((x ^ (3 : ℕ)) /. (((x ^ (4 : ℕ)) - (x ^ (2 : ℕ))) + 2)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((x ^ (2 : ℕ)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}) := by
  sorry

theorem proof_gap_exercise_1842_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((x ^ (3 : ℕ)) /. (((x ^ (4 : ℕ)) - (x ^ (2 : ℕ))) + 2)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((x ^ (2 : ℕ)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = (((x ^ (2 : ℕ)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_6 x) = ((1 /. 2) * (F_5 x)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x) = (((((x ^ (2 : ℕ)) - (1 /. 2)) + (1 /. 2)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) - (1 /. 2))) x))) ∧ ((F_8 x) = ((1 /. 2) * (F_7 x)))))))}) := by
  sorry

theorem proof_gap_exercise_1842_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((x ^ (3 : ℕ)) /. (((x ^ (4 : ℕ)) - (x ^ (2 : ℕ))) + 2)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((x ^ (2 : ℕ)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}))
  (h3 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = (((x ^ (2 : ℕ)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_6 x) = ((1 /. 2) * (F_5 x)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x) = (((((x ^ (2 : ℕ)) - (1 /. 2)) + (1 /. 2)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) - (1 /. 2))) x))) ∧ ((F_8 x) = ((1 /. 2) * (F_7 x)))))))}))
  : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_9 t) x) = (((((x ^ (2 : ℕ)) - (1 /. 2)) + (1 /. 2)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) - (1 /. 2))) x))) ∧ ((F_10 x) = ((1 /. 2) * (F_9 x)))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)) (F_13 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_11 t) x) = ((iteratedDeriv 1 (fun t => (((t ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ))) x) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4)))) ∧ ((iteratedDeriv 1 (fun t => F_13 t) x) = ((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) - (1 /. 2))) x) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (((Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)) /. 2) ^ (2 : ℕ)))))) ∧ ((F_15 x) = (((1 /. 4) * (F_11 x)) + ((1 /. 4) * (F_13 x)))))))))}) := by
  sorry

theorem proof_gap_exercise_1842_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((x ^ (3 : ℕ)) /. (((x ^ (4 : ℕ)) - (x ^ (2 : ℕ))) + 2)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = (((x ^ (2 : ℕ)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}))
  (h3 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = (((x ^ (2 : ℕ)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => (t ^ (2 : ℕ))) x))) ∧ ((F_6 x) = ((1 /. 2) * (F_5 x)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x) = (((((x ^ (2 : ℕ)) - (1 /. 2)) + (1 /. 2)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) - (1 /. 2))) x))) ∧ ((F_8 x) = ((1 /. 2) * (F_7 x)))))))}))
  (h4 : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_9 t) x) = (((((x ^ (2 : ℕ)) - (1 /. 2)) + (1 /. 2)) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4))) * (iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) - (1 /. 2))) x))) ∧ ((F_10 x) = ((1 /. 2) * (F_9 x)))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)) (F_13 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_11 t) x) = ((iteratedDeriv 1 (fun t => (((t ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ))) x) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (7 /. 4)))) ∧ ((iteratedDeriv 1 (fun t => F_13 t) x) = ((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) - (1 /. 2))) x) /. ((((x ^ (2 : ℕ)) - (1 /. 2)) ^ (2 : ℕ)) + (((Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)) /. 2) ^ (2 : ℕ)))))) ∧ ((F_15 x) = (((1 /. 4) * (F_11 x)) + ((1 /. 4) * (F_13 x)))))))))}))
  : ({F_16 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_16 t) x) = (((x ^ (3 : ℕ)) /. (((x ^ (4 : ℕ)) - (x ^ (2 : ℕ))) + 2)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_17 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_17 x) = ((((1 /. 4) * (Real.log (((x ^ (4 : ℕ)) - (x ^ (2 : ℕ))) + 2))) + ((1 /. (2 * (Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.arctan (((2 * (x ^ (2 : ℕ))) - 1) /. (Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)))))) + C_1))))))}) := by
  sorry
