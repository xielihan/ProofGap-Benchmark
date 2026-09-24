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

-- exercise: exercise_2095

theorem proof_gap_exercise_2095_1
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) ∧ (x ≠ 2))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.exp (2 * x_1)) /. (((x_1 ^ (2 : ℕ)) - (3 * x_1)) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_2095_2
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) ∧ (x ≠ 2))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.exp (2 * x_1)) /. (((x_1 ^ (2 : ℕ)) - (3 * x_1)) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)) (F_6 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 2)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_6 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 1)) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_7 x_1) = ((F_5 x_1) - (F_6 x_1))))))))}) := by
  sorry

theorem proof_gap_exercise_2095_3
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) ∧ (x ≠ 2))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.exp (2 * x_1)) /. (((x_1 ^ (2 : ℕ)) - (3 * x_1)) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)) (F_6 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 2)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_6 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 1)) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_7 x_1) = ((F_5 x_1) - (F_6 x_1))))))))}))
  : ({F_8 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_8 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 2)) → (((iteratedDeriv 1 (fun t => F_9 t) x_1) = (((Real.exp (2 * (x_1 - 2))) * (iteratedDeriv 1 (fun t => (t - 2)) x_1)) /. (x_1 - 2))) ∧ ((F_10 x_1) = ((Real.exp (4 : ℝ)) * (F_9 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_2095_4
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) ∧ (x ≠ 2))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.exp (2 * x_1)) /. (((x_1 ^ (2 : ℕ)) - (3 * x_1)) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)) (F_6 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 2)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_6 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 1)) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_7 x_1) = ((F_5 x_1) - (F_6 x_1))))))))}))
  (h5 : ({F_8 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_8 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 2)) → (((iteratedDeriv 1 (fun t => F_9 t) x_1) = (((Real.exp (2 * (x_1 - 2))) * (iteratedDeriv 1 (fun t => (t - 2)) x_1)) /. (x_1 - 2))) ∧ ((F_10 x_1) = ((Real.exp (4 : ℝ)) * (F_9 x_1)))))))}))
  : ({F_11 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_13 : (ℝ -> ℝ) | (exists (F_12 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) → (((iteratedDeriv 1 (fun t => F_12 t) x_1) = (((Real.exp (2 * (x_1 - 1))) * (iteratedDeriv 1 (fun t => (t - 1)) x_1)) /. (x_1 - 1))) ∧ ((F_13 x_1) = ((Real.exp (2 : ℝ)) * (F_12 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_2095_5
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) ∧ (x ≠ 2))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((Real.exp (2 * x_1)) /. (((x_1 ^ (2 : ℕ)) - (3 * x_1)) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((Real.exp (2 * x_1)) /. ((x_1 - 2) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)) (F_6 : (ℝ -> ℝ)), (True ∧ (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((((iteratedDeriv 1 (fun t => F_5 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 2)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((iteratedDeriv 1 (fun t => F_6 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 1)) * (iteratedDeriv 1 (fun t => t) x_1)))) ∧ ((F_7 x_1) = ((F_5 x_1) - (F_6 x_1))))))))}))
  (h5 : ({F_8 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_8 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 2)) → (((iteratedDeriv 1 (fun t => F_9 t) x_1) = (((Real.exp (2 * (x_1 - 2))) * (iteratedDeriv 1 (fun t => (t - 2)) x_1)) /. (x_1 - 2))) ∧ ((F_10 x_1) = ((Real.exp (4 : ℝ)) * (F_9 x_1)))))))}))
  (h6 : ({F_11 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_11 t) x_1) = (((Real.exp (2 * x_1)) /. (x_1 - 1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_13 : (ℝ -> ℝ) | (exists (F_12 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) → (((iteratedDeriv 1 (fun t => F_12 t) x_1) = (((Real.exp (2 * (x_1 - 1))) * (iteratedDeriv 1 (fun t => (t - 1)) x_1)) /. (x_1 - 1))) ∧ ((F_13 x_1) = ((Real.exp (2 : ℝ)) * (F_12 x_1)))))))}))
  : ({F_14 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((iteratedDeriv 1 (fun t => F_14 t) x_1) = (((Real.exp (2 * x_1)) /. (((x_1 ^ (2 : ℕ)) - (3 * x_1)) + 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 1)) ∧ (x_1 ≠ 2)) → ((F_15 x_1) = ((((Real.exp (4 : ℝ)) * (li (Real.exp ((2 * x_1) - 4)))) - ((Real.exp (2 : ℝ)) * (li (Real.exp ((2 * x_1) - 2))))) + C_1))))))}) := by
  sorry
