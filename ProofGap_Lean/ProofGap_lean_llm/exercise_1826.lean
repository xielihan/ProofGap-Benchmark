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

abbrev SetValueAt (S : Set (ℝ -> ℝ)) (x value : ℝ) : Prop := ∃ F ∈ S, F x = value

-- exercise: exercise_1826

theorem proof_gap_exercise_1826_1
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 * (Real.cos (Real.log x_1))) * (1 /. x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_5 x_1) = ((x_1 * (Real.sin (Real.log x_1))) - (F_3 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1826_2
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 * (Real.cos (Real.log x_1))) * (1 /. x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_5 x_1) = ((x_1 * (Real.sin (Real.log x_1))) - (F_3 x_1)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_9 x_1) = (((x_1 * (Real.sin (Real.log x_1))) - (x_1 * (Real.cos (Real.log x_1)))) - (F_7 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1826_3
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 * (Real.cos (Real.log x_1))) * (1 /. x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_5 x_1) = ((x_1 * (Real.sin (Real.log x_1))) - (F_3 x_1)))))))}))
  (h3 : ({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_9 x_1) = (((x_1 * (Real.sin (Real.log x_1))) - (x_1 * (Real.cos (Real.log x_1)))) - (F_7 x_1)))))))}))
  : SetValueAt ({F_11 : (ℝ -> ℝ) | (exists (F_10 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_10 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_11 x_1) = (2 * (F_10 x_1)))))))} : Set (ℝ -> ℝ)) x (x * ((Real.sin (Real.log x)) - (Real.cos (Real.log x)))) := by
  sorry

theorem proof_gap_exercise_1826_4
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((x_1 * (Real.cos (Real.log x_1))) * (1 /. x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_5 x_1) = ((x_1 * (Real.sin (Real.log x_1))) - (F_3 x_1)))))))}))
  (h3 : ({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_7 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_9 x_1) = (((x_1 * (Real.sin (Real.log x_1))) - (x_1 * (Real.cos (Real.log x_1)))) - (F_7 x_1)))))))}))
  (h4 : SetValueAt ({F_11 : (ℝ -> ℝ) | (exists (F_10 : (ℝ -> ℝ)), (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((iteratedDeriv 1 (fun t => F_10 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1))) ∧ ((F_11 x_1) = (2 * (F_10 x_1)))))))} : Set (ℝ -> ℝ)) x (x * ((Real.sin (Real.log x)) - (Real.cos (Real.log x)))))
  : ({F_12 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((iteratedDeriv 1 (fun t => F_12 t) x_1) = ((Real.sin (Real.log x_1)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_13 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((F_13 x_1) = (((x_1 /. 2) * ((Real.sin (Real.log x_1)) - (Real.cos (Real.log x_1)))) + C))))))}) := by
  sorry
