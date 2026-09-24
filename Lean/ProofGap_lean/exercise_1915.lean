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

-- exercise: exercise_1915

theorem proof_gap_exercise_1915_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (7 : ℕ))) ≠ 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) = ((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1915_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (7 : ℕ))) ≠ 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) = ((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ)))))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) := by
  sorry

theorem proof_gap_exercise_1915_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (7 : ℕ))) ≠ 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) = ((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ)))))))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = (((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((iteratedDeriv 1 (fun t => (1 + (t ^ (7 : ℕ)))) x) /. (1 + (x ^ (7 : ℕ))))) ∧ ((F_8 x) = ((Real.log |(x)|) - ((2 /. 7) * (F_5 x))))))))}) := by
  sorry

theorem proof_gap_exercise_1915_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (7 : ℕ))) ≠ 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) = ((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ)))))))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h7 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = (((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((iteratedDeriv 1 (fun t => (1 + (t ^ (7 : ℕ)))) x) /. (1 + (x ^ (7 : ℕ))))) ∧ ((F_8 x) = ((Real.log |(x)|) - ((2 /. 7) * (F_5 x))))))))}))
  : ({F_12 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((iteratedDeriv 1 (fun t => F_9 t) x) = ((iteratedDeriv 1 (fun t => (1 + (t ^ (7 : ℕ)))) x) /. (1 + (x ^ (7 : ℕ))))) ∧ ((F_12 x) = ((Real.log |(x)|) - ((2 /. 7) * (F_9 x))))))))}) = ({F_13 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((F_13 x) = (((Real.log |(x)|) - ((2 /. 7) * (Real.log |((1 + (x ^ (7 : ℕ))))|))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1915_5
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (7 : ℕ))) ≠ 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) = ((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ)))))))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h7 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = (((1 /. x) - ((2 * (x ^ (6 : ℕ))) /. (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((iteratedDeriv 1 (fun t => (1 + (t ^ (7 : ℕ)))) x) /. (1 + (x ^ (7 : ℕ))))) ∧ ((F_8 x) = ((Real.log |(x)|) - ((2 /. 7) * (F_5 x))))))))}))
  (h8 : ({F_12 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → (((iteratedDeriv 1 (fun t => F_9 t) x) = ((iteratedDeriv 1 (fun t => (1 + (t ^ (7 : ℕ)))) x) /. (1 + (x ^ (7 : ℕ))))) ∧ ((F_12 x) = ((Real.log |(x)|) - ((2 /. 7) * (F_9 x))))))))}) = ({F_13 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((F_13 x) = (((Real.log |(x)|) - ((2 /. 7) * (Real.log |((1 + (x ^ (7 : ℕ))))|))) + C_1))))))}))
  : ({F_14 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((iteratedDeriv 1 (fun t => F_14 t) x) = (((1 - (x ^ (7 : ℕ))) /. (x * (1 + (x ^ (7 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x ^ (7 : ℕ))) ≠ 0)) → ((F_15 x) = (((1 /. 7) * (Real.log ((|(x)| ^ (7 : ℕ)) /. ((1 + (x ^ (7 : ℕ))) ^ (2 : ℕ))))) + C_1))))))}) := by
  sorry
