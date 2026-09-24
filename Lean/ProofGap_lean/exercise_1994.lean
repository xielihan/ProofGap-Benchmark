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

-- exercise: exercise_1994

theorem proof_gap_exercise_1994_1
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((Real.sin x_1) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1994_2
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((Real.sin x_1) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 4) * (F_5 x_1)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * (1 + (Real.cos (2 * x_1)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_8 x_1) = ((1 /. 8) * (F_7 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1994_3
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((Real.sin x_1) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 4) * (F_5 x_1)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * (1 + (Real.cos (2 * x_1)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_8 x_1) = ((1 /. 8) * (F_7 x_1)))))))}))
  : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_9 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * (1 + (Real.cos (2 * x_1)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_10 x_1) = ((1 /. 8) * (F_9 x_1)))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)) (F_13 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((1 - (Real.cos (4 * x_1))) /. 2) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_13 t) x_1) = (((Real.sin (2 * x_1)) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x_1)))) ∧ ((F_15 x_1) = (((1 /. 8) * (F_11 x_1)) + ((1 /. 16) * (F_13 x_1)))))))))}) := by
  sorry

theorem proof_gap_exercise_1994_4
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((Real.sin x_1) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_4 x_1) = ((1 /. 4) * (F_3 x_1)))))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 4) * (F_5 x_1)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * (1 + (Real.cos (2 * x_1)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_8 x_1) = ((1 /. 8) * (F_7 x_1)))))))}))
  (h5 : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_9 t) x_1) = ((((Real.sin (2 * x_1)) ^ (2 : ℕ)) * (1 + (Real.cos (2 * x_1)))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_10 x_1) = ((1 /. 8) * (F_9 x_1)))))))}) = ({F_15 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)) (F_13 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((1 - (Real.cos (4 * x_1))) /. 2) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_13 t) x_1) = (((Real.sin (2 * x_1)) ^ (2 : ℕ)) * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x_1)))) ∧ ((F_15 x_1) = (((1 /. 8) * (F_11 x_1)) + ((1 /. 16) * (F_13 x_1)))))))))}))
  : ({F_16 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_16 t) x_1) = ((((Real.sin x_1) ^ (2 : ℕ)) * ((Real.cos x_1) ^ (4 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_17 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_17 x_1) = ((((x_1 /. 16) - ((1 /. 64) * (Real.sin (4 * x_1)))) + ((1 /. 48) * ((Real.sin (2 * x_1)) ^ (3 : ℕ)))) + C_1))))))}) := by
  sorry
