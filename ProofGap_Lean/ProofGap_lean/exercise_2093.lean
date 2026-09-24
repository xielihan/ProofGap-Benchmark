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

-- exercise: exercise_2093

theorem proof_gap_exercise_2093_1
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((1 - (2 /. x)) ^ (2 : ℕ)) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) := by
  sorry

theorem proof_gap_exercise_2093_2
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((1 - (2 /. x)) ^ (2 : ℕ)) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((Real.exp x) * (iteratedDeriv 1 (fun t => (1 /. t)) x))) ∧ ((F_8 x) = (((Real.exp x) - (4 * (li (Real.exp x)))) - (4 * (F_5 x))))))))}) := by
  sorry

theorem proof_gap_exercise_2093_3
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((1 - (2 /. x)) ^ (2 : ℕ)) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((Real.exp x) * (iteratedDeriv 1 (fun t => (1 /. t)) x))) ∧ ((F_8 x) = (((Real.exp x) - (4 * (li (Real.exp x)))) - (4 * (F_5 x))))))))}))
  : ({F_12 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_9 t) x) = ((Real.exp x) * (iteratedDeriv 1 (fun t => (1 /. t)) x))) ∧ ((F_12 x) = (((Real.exp x) - (4 * (li (Real.exp x)))) - (4 * (F_9 x))))))))}) = ({F_16 : (ℝ -> ℝ) | (exists (F_13 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_13 t) x) = (((Real.exp x) /. x) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_16 x) = ((((Real.exp x) - (4 * (li (Real.exp x)))) - ((4 /. x) * (Real.exp x))) + (4 * (F_13 x))))))))}) := by
  sorry

theorem proof_gap_exercise_2093_4
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((1 - (2 /. x)) ^ (2 : ℕ)) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((Real.exp x) * (iteratedDeriv 1 (fun t => (1 /. t)) x))) ∧ ((F_8 x) = (((Real.exp x) - (4 * (li (Real.exp x)))) - (4 * (F_5 x))))))))}))
  (h5 : ({F_12 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_9 t) x) = ((Real.exp x) * (iteratedDeriv 1 (fun t => (1 /. t)) x))) ∧ ((F_12 x) = (((Real.exp x) - (4 * (li (Real.exp x)))) - (4 * (F_9 x))))))))}) = ({F_16 : (ℝ -> ℝ) | (exists (F_13 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_13 t) x) = (((Real.exp x) /. x) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_16 x) = ((((Real.exp x) - (4 * (li (Real.exp x)))) - ((4 /. x) * (Real.exp x))) + (4 * (F_13 x))))))))}))
  : ({F_20 : (ℝ -> ℝ) | (exists (F_17 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_17 t) x) = (((Real.exp x) /. x) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_20 x) = (((-(4 : ℝ)) * (li (Real.exp x))) + (4 * (F_17 x))))))))}) = ({F_21 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((F_21 x) = C_1)))))}) := by
  sorry

theorem proof_gap_exercise_2093_5
  (li : (ℝ -> ℝ))
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((1 - (2 /. x)) ^ (2 : ℕ)) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((1 - (4 /. x)) + (4 /. (x ^ (2 : ℕ)))) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((Real.exp x) * (iteratedDeriv 1 (fun t => (1 /. t)) x))) ∧ ((F_8 x) = (((Real.exp x) - (4 * (li (Real.exp x)))) - (4 * (F_5 x))))))))}))
  (h5 : ({F_12 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_9 t) x) = ((Real.exp x) * (iteratedDeriv 1 (fun t => (1 /. t)) x))) ∧ ((F_12 x) = (((Real.exp x) - (4 * (li (Real.exp x)))) - (4 * (F_9 x))))))))}) = ({F_16 : (ℝ -> ℝ) | (exists (F_13 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_13 t) x) = (((Real.exp x) /. x) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_16 x) = ((((Real.exp x) - (4 * (li (Real.exp x)))) - ((4 /. x) * (Real.exp x))) + (4 * (F_13 x))))))))}))
  (h6 : ({F_20 : (ℝ -> ℝ) | (exists (F_17 : (ℝ -> ℝ)), (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((iteratedDeriv 1 (fun t => F_17 t) x) = (((Real.exp x) /. x) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_20 x) = (((-(4 : ℝ)) * (li (Real.exp x))) + (4 * (F_17 x))))))))}) = ({F_21 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((F_21 x) = C_1)))))}))
  : ({F_22 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => F_22 t) x) = ((((1 - (2 /. x)) ^ (2 : ℕ)) * (Real.exp x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_23 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((F_23 x) = (((Real.exp x) * (1 - (4 /. x))) + C_1))))))}) := by
  sorry
