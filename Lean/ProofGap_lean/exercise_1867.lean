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

-- exercise: exercise_1867

theorem proof_gap_exercise_1867_1
  (x : ℝ)
  (C : ℝ)
  (h1 : (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ (-(2 : ℝ)))) ∧ (x ≠ (-(3 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : A = (-(1 /. 2)))
  (h4 : B = 2)
  (h5 : D = (-(3 /. 2)))
  : (x /. (((x + 1) * (x + 2)) * (x + 3))) = (((A /. (x + 1)) + (B /. (x + 2))) + (D /. (x + 3))) := by
  sorry

theorem proof_gap_exercise_1867_2
  (x : ℝ)
  (C : ℝ)
  (h1 : (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ (-(2 : ℝ)))) ∧ (x ≠ (-(3 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : A = (-(1 /. 2)))
  (h4 : B = 2)
  (h5 : D = (-(3 /. 2)))
  (h6 : (x /. (((x + 1) * (x + 2)) * (x + 3))) = (((A /. (x + 1)) + (B /. (x + 2))) + (D /. (x + 3))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((x_1 /. (((x_1 + 1) * (x_1 + 2)) * (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((((-(1 /. 2)) /. (x_1 + 1)) + (2 /. (x_1 + 2))) + ((-(3 /. 2)) /. (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_1867_3
  (x : ℝ)
  (C : ℝ)
  (h1 : (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ (-(2 : ℝ)))) ∧ (x ≠ (-(3 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : A = (-(1 /. 2)))
  (h4 : B = 2)
  (h5 : D = (-(3 /. 2)))
  (h6 : (x /. (((x + 1) * (x + 2)) * (x + 3))) = (((A /. (x + 1)) + (B /. (x + 2))) + (D /. (x + 3))))
  (h7 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((x_1 /. (((x_1 + 1) * (x_1 + 2)) * (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((((-(1 /. 2)) /. (x_1 + 1)) + (2 /. (x_1 + 2))) + ((-(3 /. 2)) /. (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((((-(1 /. 2)) /. (x_1 + 1)) + (2 /. (x_1 + 2))) + ((-(3 /. 2)) /. (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((F_5 x_1) = (((((-(1 /. 2)) * (Real.log |((x_1 + 1))|)) + (2 * (Real.log |((x_1 + 2))|))) - ((3 /. 2) * (Real.log |((x_1 + 3))|))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1867_4
  (x : ℝ)
  (C : ℝ)
  (h1 : (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ (-(2 : ℝ)))) ∧ (x ≠ (-(3 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : A = (-(1 /. 2)))
  (h4 : B = 2)
  (h5 : D = (-(3 /. 2)))
  (h6 : (x /. (((x + 1) * (x + 2)) * (x + 3))) = (((A /. (x + 1)) + (B /. (x + 2))) + (D /. (x + 3))))
  (h7 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((x_1 /. (((x_1 + 1) * (x_1 + 2)) * (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((((-(1 /. 2)) /. (x_1 + 1)) + (2 /. (x_1 + 2))) + ((-(3 /. 2)) /. (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h8 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((((-(1 /. 2)) /. (x_1 + 1)) + (2 /. (x_1 + 2))) + ((-(3 /. 2)) /. (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((F_5 x_1) = (((((-(1 /. 2)) * (Real.log |((x_1 + 1))|)) + (2 * (Real.log |((x_1 + 2))|))) - ((3 /. 2) * (Real.log |((x_1 + 3))|))) + C_1))))))}))
  : ({F_6 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((iteratedDeriv 1 (fun t => F_6 t) x_1) = ((x_1 /. (((x_1 + 1) * (x_1 + 2)) * (x_1 + 3))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ (-(3 : ℝ)))) → ((F_7 x_1) = (((1 /. 2) * (Real.log |((((x_1 + 2) ^ (4 : ℕ)) /. ((x_1 + 1) * ((x_1 + 3) ^ (3 : ℕ)))))|)) + C_1))))))}) := by
  sorry
