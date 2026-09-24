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

-- exercise: exercise_1821

theorem proof_gap_exercise_1821_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.sin x) ^ (2 : ℕ)) = ((1 /. 2) * (1 - (Real.cos (2 * x))))))) := by
  sorry

theorem proof_gap_exercise_1821_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.sin x) ^ (2 : ℕ)) = ((1 /. 2) * (1 - (Real.cos (2 * x))))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x * ((Real.sin x) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}) := by
  sorry

theorem proof_gap_exercise_1821_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.sin x) ^ (2 : ℕ)) = ((1 /. 2) * (1 - (Real.cos (2 * x))))))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x * ((Real.sin x) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((1 /. 2) * (F_5 x)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)) (F_9 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_7 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_9 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_11 x) = (((1 /. 2) * (F_7 x)) - ((1 /. 2) * (F_9 x)))))))))}) := by
  sorry

theorem proof_gap_exercise_1821_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.sin x) ^ (2 : ℕ)) = ((1 /. 2) * (1 - (Real.cos (2 * x))))))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x * ((Real.sin x) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((1 /. 2) * (F_5 x)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)) (F_9 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_7 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_9 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_11 x) = (((1 /. 2) * (F_7 x)) - ((1 /. 2) * (F_9 x)))))))))}))
  : ({F_16 : (ℝ -> ℝ) | (exists (F_12 : (ℝ -> ℝ)) (F_14 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_12 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_14 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_16 x) = (((1 /. 2) * (F_12 x)) - ((1 /. 2) * (F_14 x)))))))))}) = ({F_20 : (ℝ -> ℝ) | (exists (F_17 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_17 t) x) = (x * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x))) ∧ ((F_20 x) = (((1 /. 4) * (x ^ (2 : ℕ))) - ((1 /. 4) * (F_17 x))))))))}) := by
  sorry

theorem proof_gap_exercise_1821_5
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.sin x) ^ (2 : ℕ)) = ((1 /. 2) * (1 - (Real.cos (2 * x))))))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x * ((Real.sin x) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((1 /. 2) * (F_5 x)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)) (F_9 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_7 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_9 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_11 x) = (((1 /. 2) * (F_7 x)) - ((1 /. 2) * (F_9 x)))))))))}))
  (h5 : ({F_16 : (ℝ -> ℝ) | (exists (F_12 : (ℝ -> ℝ)) (F_14 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_12 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_14 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_16 x) = (((1 /. 2) * (F_12 x)) - ((1 /. 2) * (F_14 x)))))))))}) = ({F_20 : (ℝ -> ℝ) | (exists (F_17 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_17 t) x) = (x * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x))) ∧ ((F_20 x) = (((1 /. 4) * (x ^ (2 : ℕ))) - ((1 /. 4) * (F_17 x))))))))}))
  : ({F_24 : (ℝ -> ℝ) | (exists (F_21 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_21 t) x) = (x * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x))) ∧ ((F_24 x) = (((1 /. 4) * (x ^ (2 : ℕ))) - ((1 /. 4) * (F_21 x))))))))}) = ({F_28 : (ℝ -> ℝ) | (exists (F_25 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_25 t) x) = ((Real.sin (2 * x)) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_28 x) = ((((1 /. 4) * (x ^ (2 : ℕ))) - (((1 /. 4) * x) * (Real.sin (2 * x)))) + ((1 /. 4) * (F_25 x))))))))}) := by
  sorry

theorem proof_gap_exercise_1821_6
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.sin x) ^ (2 : ℕ)) = ((1 /. 2) * (1 - (Real.cos (2 * x))))))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x * ((Real.sin x) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((1 /. 2) * (F_5 x)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)) (F_9 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_7 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_9 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_11 x) = (((1 /. 2) * (F_7 x)) - ((1 /. 2) * (F_9 x)))))))))}))
  (h5 : ({F_16 : (ℝ -> ℝ) | (exists (F_12 : (ℝ -> ℝ)) (F_14 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_12 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_14 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_16 x) = (((1 /. 2) * (F_12 x)) - ((1 /. 2) * (F_14 x)))))))))}) = ({F_20 : (ℝ -> ℝ) | (exists (F_17 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_17 t) x) = (x * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x))) ∧ ((F_20 x) = (((1 /. 4) * (x ^ (2 : ℕ))) - ((1 /. 4) * (F_17 x))))))))}))
  (h6 : ({F_24 : (ℝ -> ℝ) | (exists (F_21 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_21 t) x) = (x * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x))) ∧ ((F_24 x) = (((1 /. 4) * (x ^ (2 : ℕ))) - ((1 /. 4) * (F_21 x))))))))}) = ({F_28 : (ℝ -> ℝ) | (exists (F_25 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_25 t) x) = ((Real.sin (2 * x)) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_28 x) = ((((1 /. 4) * (x ^ (2 : ℕ))) - (((1 /. 4) * x) * (Real.sin (2 * x)))) + ((1 /. 4) * (F_25 x))))))))}))
  : ({F_29 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_29 t) x) = ((Real.sin (2 * x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_30 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_30 x) = (((-(1 /. 2)) * (Real.cos (2 * x))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1821_7
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((Real.sin x) ^ (2 : ℕ)) = ((1 /. 2) * (1 - (Real.cos (2 * x))))))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((x * ((Real.sin x) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_4 x) = ((1 /. 2) * (F_3 x)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x * (1 - (Real.cos (2 * x)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_6 x) = ((1 /. 2) * (F_5 x)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)) (F_9 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_7 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_9 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_11 x) = (((1 /. 2) * (F_7 x)) - ((1 /. 2) * (F_9 x)))))))))}))
  (h5 : ({F_16 : (ℝ -> ℝ) | (exists (F_12 : (ℝ -> ℝ)) (F_14 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_12 t) x) = (x * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_14 t) x) = ((x * (Real.cos (2 * x))) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_16 x) = (((1 /. 2) * (F_12 x)) - ((1 /. 2) * (F_14 x)))))))))}) = ({F_20 : (ℝ -> ℝ) | (exists (F_17 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_17 t) x) = (x * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x))) ∧ ((F_20 x) = (((1 /. 4) * (x ^ (2 : ℕ))) - ((1 /. 4) * (F_17 x))))))))}))
  (h6 : ({F_24 : (ℝ -> ℝ) | (exists (F_21 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_21 t) x) = (x * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x))) ∧ ((F_24 x) = (((1 /. 4) * (x ^ (2 : ℕ))) - ((1 /. 4) * (F_21 x))))))))}) = ({F_28 : (ℝ -> ℝ) | (exists (F_25 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_25 t) x) = ((Real.sin (2 * x)) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_28 x) = ((((1 /. 4) * (x ^ (2 : ℕ))) - (((1 /. 4) * x) * (Real.sin (2 * x)))) + ((1 /. 4) * (F_25 x))))))))}))
  (h7 : ({F_29 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_29 t) x) = ((Real.sin (2 * x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_30 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_30 x) = (((-(1 /. 2)) * (Real.cos (2 * x))) + C_1))))))}))
  : ({F_31 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_31 t) x) = ((x * ((Real.sin x) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_32 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_32 x) = (((((1 /. 4) * (x ^ (2 : ℕ))) - ((x /. 4) * (Real.sin (2 * x)))) - ((1 /. 8) * (Real.cos (2 * x)))) + C_1))))))}) := by
  sorry
