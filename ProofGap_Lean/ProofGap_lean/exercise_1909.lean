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

-- exercise: exercise_1909

theorem proof_gap_exercise_1909_1
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (11 : ℕ)) /. (((x_1 ^ (8 : ℕ)) + (3 * (x_1 ^ (4 : ℕ)))) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1909_2
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (11 : ℕ)) /. (((x_1 ^ (8 : ℕ)) + (3 * (x_1 ^ (4 : ℕ)))) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_6 x_1) = ((1 /. 4) * (F_5 x_1)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((1 - (((3 * (x_1 ^ (4 : ℕ))) + 2) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2)))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_8 x_1) = ((1 /. 4) * (F_7 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1909_3
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (11 : ℕ)) /. (((x_1 ^ (8 : ℕ)) + (3 * (x_1 ^ (4 : ℕ)))) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_6 x_1) = ((1 /. 4) * (F_5 x_1)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((1 - (((3 * (x_1 ^ (4 : ℕ))) + 2) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2)))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_8 x_1) = ((1 /. 4) * (F_7 x_1)))))))}))
  : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_9 t) x_1) = ((1 - (((3 * (x_1 ^ (4 : ℕ))) + 2) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2)))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_10 x_1) = ((1 /. 4) * (F_9 x_1)))))))}) = ({F_12 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((1 + (1 /. ((x_1 ^ (4 : ℕ)) + 1))) - (4 /. ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_12 x_1) = ((1 /. 4) * (F_11 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1909_4
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (11 : ℕ)) /. (((x_1 ^ (8 : ℕ)) + (3 * (x_1 ^ (4 : ℕ)))) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_6 x_1) = ((1 /. 4) * (F_5 x_1)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((1 - (((3 * (x_1 ^ (4 : ℕ))) + 2) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2)))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_8 x_1) = ((1 /. 4) * (F_7 x_1)))))))}))
  (h5 : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_9 t) x_1) = ((1 - (((3 * (x_1 ^ (4 : ℕ))) + 2) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2)))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_10 x_1) = ((1 /. 4) * (F_9 x_1)))))))}) = ({F_12 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((1 + (1 /. ((x_1 ^ (4 : ℕ)) + 1))) - (4 /. ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_12 x_1) = ((1 /. 4) * (F_11 x_1)))))))}))
  : ({F_14 : (ℝ -> ℝ) | (exists (F_13 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_13 t) x_1) = (((1 + (1 /. ((x_1 ^ (4 : ℕ)) + 1))) - (4 /. ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_14 x_1) = ((1 /. 4) * (F_13 x_1)))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_15 x_1) = ((((x_1 ^ (4 : ℕ)) /. 4) + ((1 /. 4) * (Real.log (((x_1 ^ (4 : ℕ)) + 1) /. (((x_1 ^ (4 : ℕ)) + 2) ^ (4 : ℕ)))))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1909_5
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (11 : ℕ)) /. (((x_1 ^ (8 : ℕ)) + (3 * (x_1 ^ (4 : ℕ)))) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((x_1 ^ (8 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_6 x_1) = ((1 /. 4) * (F_5 x_1)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((1 - (((3 * (x_1 ^ (4 : ℕ))) + 2) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2)))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_8 x_1) = ((1 /. 4) * (F_7 x_1)))))))}))
  (h5 : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_9 t) x_1) = ((1 - (((3 * (x_1 ^ (4 : ℕ))) + 2) /. (((x_1 ^ (4 : ℕ)) + 1) * ((x_1 ^ (4 : ℕ)) + 2)))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_10 x_1) = ((1 /. 4) * (F_9 x_1)))))))}) = ({F_12 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((1 + (1 /. ((x_1 ^ (4 : ℕ)) + 1))) - (4 /. ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_12 x_1) = ((1 /. 4) * (F_11 x_1)))))))}))
  (h6 : ({F_14 : (ℝ -> ℝ) | (exists (F_13 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_13 t) x_1) = (((1 + (1 /. ((x_1 ^ (4 : ℕ)) + 1))) - (4 /. ((x_1 ^ (4 : ℕ)) + 2))) * (iteratedDeriv 1 (fun t => (t ^ (4 : ℕ))) x_1))) ∧ ((F_14 x_1) = ((1 /. 4) * (F_13 x_1)))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_15 x_1) = ((((x_1 ^ (4 : ℕ)) /. 4) + ((1 /. 4) * (Real.log (((x_1 ^ (4 : ℕ)) + 1) /. (((x_1 ^ (4 : ℕ)) + 2) ^ (4 : ℕ)))))) + C_1))))))}))
  : ({F_16 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_16 t) x_1) = (((x_1 ^ (11 : ℕ)) /. (((x_1 ^ (8 : ℕ)) + (3 * (x_1 ^ (4 : ℕ)))) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_17 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_17 x_1) = ((((x_1 ^ (4 : ℕ)) /. 4) + ((1 /. 4) * (Real.log (((x_1 ^ (4 : ℕ)) + 1) /. (((x_1 ^ (4 : ℕ)) + 2) ^ (4 : ℕ)))))) + C_1))))))}) := by
  sorry
