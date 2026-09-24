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

-- exercise: exercise_1992

theorem proof_gap_exercise_1992_1
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_1992_2
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((((1 - (3 * (Real.cos (2 * x_1)))) + (3 * ((Real.cos (2 * x_1)) ^ (2 : ℕ)))) - ((Real.cos (2 * x_1)) ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 8) * (F_5 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1992_3
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((((1 - (3 * (Real.cos (2 * x_1)))) + (3 * ((Real.cos (2 * x_1)) ^ (2 : ℕ)))) - ((Real.cos (2 * x_1)) ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 8) * (F_5 x_1)))))))}))
  : ({F_7 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_14 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)) (F_12 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_8 t) x_1) = (((1 + (Real.cos (4 * x_1))) /. 2) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_12 t) x_1) = (((1 - ((Real.sin (2 * x_1)) ^ (2 : ℕ))) * (Real.cos (2 * x_1))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_14 x_1) = ((((x_1 /. 8) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 /. 8) * (F_8 x_1))) - ((1 /. 8) * (F_12 x_1)))))))))}) := by
  sorry

theorem proof_gap_exercise_1992_4
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((((1 - (3 * (Real.cos (2 * x_1)))) + (3 * ((Real.cos (2 * x_1)) ^ (2 : ℕ)))) - ((Real.cos (2 * x_1)) ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 8) * (F_5 x_1)))))))}))
  (h5 : ({F_7 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_14 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)) (F_12 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_8 t) x_1) = (((1 + (Real.cos (4 * x_1))) /. 2) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_12 t) x_1) = (((1 - ((Real.sin (2 * x_1)) ^ (2 : ℕ))) * (Real.cos (2 * x_1))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_14 x_1) = ((((x_1 /. 8) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 /. 8) * (F_8 x_1))) - ((1 /. 8) * (F_12 x_1)))))))))}))
  : ({F_15 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_15 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_19 : (ℝ -> ℝ) | (exists (F_16 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_16 t) x_1) = ((1 - ((Real.sin (2 * x_1)) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x_1))) ∧ ((F_19 x_1) = (((((x_1 /. 8) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 * x_1) /. 16)) + ((3 /. 64) * (Real.sin (4 * x_1)))) - ((1 /. 16) * (F_16 x_1))))))))}) := by
  sorry

theorem proof_gap_exercise_1992_5
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((((1 - (3 * (Real.cos (2 * x_1)))) + (3 * ((Real.cos (2 * x_1)) ^ (2 : ℕ)))) - ((Real.cos (2 * x_1)) ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 8) * (F_5 x_1)))))))}))
  (h5 : ({F_7 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_14 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)) (F_12 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_8 t) x_1) = (((1 + (Real.cos (4 * x_1))) /. 2) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_12 t) x_1) = (((1 - ((Real.sin (2 * x_1)) ^ (2 : ℕ))) * (Real.cos (2 * x_1))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_14 x_1) = ((((x_1 /. 8) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 /. 8) * (F_8 x_1))) - ((1 /. 8) * (F_12 x_1)))))))))}))
  (h6 : ({F_15 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_15 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_19 : (ℝ -> ℝ) | (exists (F_16 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_16 t) x_1) = ((1 - ((Real.sin (2 * x_1)) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x_1))) ∧ ((F_19 x_1) = (((((x_1 /. 8) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 * x_1) /. 16)) + ((3 /. 64) * (Real.sin (4 * x_1)))) - ((1 /. 16) * (F_16 x_1))))))))}))
  : ({F_20 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_20 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_21 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_21 x_1) = (((((((5 * x_1) /. 16) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 /. 64) * (Real.sin (4 * x_1)))) - ((1 /. 16) * (Real.sin (2 * x_1)))) + ((1 /. 48) * ((Real.sin (2 * x_1)) ^ (3 : ℕ)))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1992_6
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((((1 - (Real.cos (2 * x_1))) /. 2) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((((1 - (3 * (Real.cos (2 * x_1)))) + (3 * ((Real.cos (2 * x_1)) ^ (2 : ℕ)))) - ((Real.cos (2 * x_1)) ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_6 x_1) = ((1 /. 8) * (F_5 x_1)))))))}))
  (h5 : ({F_7 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_14 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)) (F_12 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((((iteratedDeriv 1 (fun t => F_8 t) x_1) = (((1 + (Real.cos (4 * x_1))) /. 2) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_12 t) x_1) = (((1 - ((Real.sin (2 * x_1)) ^ (2 : ℕ))) * (Real.cos (2 * x_1))) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_14 x_1) = ((((x_1 /. 8) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 /. 8) * (F_8 x_1))) - ((1 /. 8) * (F_12 x_1)))))))))}))
  (h6 : ({F_15 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_15 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_19 : (ℝ -> ℝ) | (exists (F_16 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_16 t) x_1) = ((1 - ((Real.sin (2 * x_1)) ^ (2 : ℕ))) * (iteratedDeriv 1 (fun t => (Real.sin (2 * t))) x_1))) ∧ ((F_19 x_1) = (((((x_1 /. 8) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 * x_1) /. 16)) + ((3 /. 64) * (Real.sin (4 * x_1)))) - ((1 /. 16) * (F_16 x_1))))))))}))
  (h7 : ({F_20 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_20 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_21 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_21 x_1) = (((((((5 * x_1) /. 16) - ((3 /. 16) * (Real.sin (2 * x_1)))) + ((3 /. 64) * (Real.sin (4 * x_1)))) - ((1 /. 16) * (Real.sin (2 * x_1)))) + ((1 /. 48) * ((Real.sin (2 * x_1)) ^ (3 : ℕ)))) + C_1))))))}))
  : ({F_22 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_22 t) x_1) = (((Real.sin x_1) ^ (6 : ℕ)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_23 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_23 x_1) = ((((((5 * x_1) /. 16) - ((1 /. 4) * (Real.sin (2 * x_1)))) + ((3 /. 64) * (Real.sin (4 * x_1)))) + ((1 /. 48) * ((Real.sin (2 * x_1)) ^ (3 : ℕ)))) + C_1))))))}) := by
  sorry
