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

-- exercise: exercise_1722

theorem proof_gap_exercise_1722_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 1))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((1 + x) /. (1 - x)) = ((-(1 : ℝ)) + (2 /. (1 - x)))))) := by
  sorry

theorem proof_gap_exercise_1722_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 1))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((1 + x) /. (1 - x)) = ((-(1 : ℝ)) + (2 /. (1 - x)))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 + x) /. (1 - x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((-(1 : ℝ)) + (2 /. (1 - x))) * (iteratedDeriv 1 (fun t => t) x)))))}) := by
  sorry

theorem proof_gap_exercise_1722_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 1))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((1 + x) /. (1 - x)) = ((-(1 : ℝ)) + (2 /. (1 - x)))))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 + x) /. (1 - x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((-(1 : ℝ)) + (2 /. (1 - x))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  : ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((-(1 : ℝ)) + (2 /. (1 - x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((F_4 x) = (((-x) - (2 * (Real.log |((1 - x))|))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1722_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 1))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((1 + x) /. (1 - x)) = ((-(1 : ℝ)) + (2 /. (1 - x)))))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 + x) /. (1 - x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((-(1 : ℝ)) + (2 /. (1 - x))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h6 : ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((-(1 : ℝ)) + (2 /. (1 - x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((F_4 x) = (((-x) - (2 * (Real.log |((1 - x))|))) + C_1))))))}))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 + x) /. (1 - x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((F_4 x) = (((-x) - (2 * (Real.log |((1 - x))|))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1722_5
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 1))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((1 + x) /. (1 - x)) = ((-(1 : ℝ)) + (2 /. (1 - x)))))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 + x) /. (1 - x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((-(1 : ℝ)) + (2 /. (1 - x))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h6 : ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((-(1 : ℝ)) + (2 /. (1 - x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((F_4 x) = (((-x) - (2 * (Real.log |((1 - x))|))) + C_1))))))}))
  (h7 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((1 + x) /. (1 - x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((F_4 x) = (((-x) - (2 * (Real.log |((1 - x))|))) + C_1))))))}))
  : ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = (((1 + x) /. (1 - x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((F_6 x) = (((-x) - (2 * (Real.log |((1 - x))|))) + C_1))))))}) := by
  sorry
