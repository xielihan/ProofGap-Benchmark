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

-- exercise: exercise_1869

theorem proof_gap_exercise_1869_1
  (x : ℝ)
  (C : ℝ)
  (h1 : (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ≠ 2)) ∧ (x ≠ 3))
  (h2 : C ∈ (Set.univ : Set ℝ))
  : (((x ^ (3 : ℕ)) + 1) /. (((x ^ (3 : ℕ)) - (5 * (x ^ (2 : ℕ)))) + (6 * x))) = (1 + ((((5 * (x ^ (2 : ℕ))) - (6 * x)) + 1) /. ((x * (x - 2)) * (x - 3)))) := by
  sorry

theorem proof_gap_exercise_1869_2
  (x : ℝ)
  (C : ℝ)
  (h1 : (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ≠ 2)) ∧ (x ≠ 3))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (((x ^ (3 : ℕ)) + 1) /. (((x ^ (3 : ℕ)) - (5 * (x ^ (2 : ℕ)))) + (6 * x))) = (1 + ((((5 * (x ^ (2 : ℕ))) - (6 * x)) + 1) /. ((x * (x - 2)) * (x - 3)))))
  (h4 : A = (1 /. 6))
  (h5 : B = (-(9 /. 2)))
  (h6 : D = (28 /. 3))
  : ((((5 * (x ^ (2 : ℕ))) - (6 * x)) + 1) /. ((x * (x - 2)) * (x - 3))) = (((A /. x) + (B /. (x - 2))) + (D /. (x - 3))) := by
  sorry

theorem proof_gap_exercise_1869_3
  (x : ℝ)
  (C : ℝ)
  (h1 : (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ≠ 2)) ∧ (x ≠ 3))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (((x ^ (3 : ℕ)) + 1) /. (((x ^ (3 : ℕ)) - (5 * (x ^ (2 : ℕ)))) + (6 * x))) = (1 + ((((5 * (x ^ (2 : ℕ))) - (6 * x)) + 1) /. ((x * (x - 2)) * (x - 3)))))
  (h4 : A = (1 /. 6))
  (h5 : B = (-(9 /. 2)))
  (h6 : D = (28 /. 3))
  (h7 : ((((5 * (x ^ (2 : ℕ))) - (6 * x)) + 1) /. ((x * (x - 2)) * (x - 3))) = (((A /. x) + (B /. (x - 2))) + (D /. (x - 3))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ (x_1 ≠ 2)) ∧ (x_1 ≠ 3)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (3 : ℕ)) + 1) /. (((x_1 ^ (3 : ℕ)) - (5 * (x_1 ^ (2 : ℕ)))) + (6 * x_1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ (x_1 ≠ 2)) ∧ (x_1 ≠ 3)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 + (1 /. (6 * x_1))) - (9 /. (2 * (x_1 - 2)))) + (28 /. (3 * (x_1 - 3)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_1869_4
  (x : ℝ)
  (C : ℝ)
  (h1 : (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ≠ 2)) ∧ (x ≠ 3))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (((x ^ (3 : ℕ)) + 1) /. (((x ^ (3 : ℕ)) - (5 * (x ^ (2 : ℕ)))) + (6 * x))) = (1 + ((((5 * (x ^ (2 : ℕ))) - (6 * x)) + 1) /. ((x * (x - 2)) * (x - 3)))))
  (h4 : A = (1 /. 6))
  (h5 : B = (-(9 /. 2)))
  (h6 : D = (28 /. 3))
  (h7 : ((((5 * (x ^ (2 : ℕ))) - (6 * x)) + 1) /. ((x * (x - 2)) * (x - 3))) = (((A /. x) + (B /. (x - 2))) + (D /. (x - 3))))
  (h8 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ (x_1 ≠ 2)) ∧ (x_1 ≠ 3)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (3 : ℕ)) + 1) /. (((x_1 ^ (3 : ℕ)) - (5 * (x_1 ^ (2 : ℕ)))) + (6 * x_1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ (x_1 ≠ 2)) ∧ (x_1 ≠ 3)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 + (1 /. (6 * x_1))) - (9 /. (2 * (x_1 - 2)))) + (28 /. (3 * (x_1 - 3)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ (x_1 ≠ 2)) ∧ (x_1 ≠ 3)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((((x_1 ^ (3 : ℕ)) + 1) /. (((x_1 ^ (3 : ℕ)) - (5 * (x_1 ^ (2 : ℕ)))) + (6 * x_1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ (x_1 ≠ 2)) ∧ (x_1 ≠ 3)) → ((F_5 x_1) = ((((x_1 + ((1 /. 6) * (Real.log |(x_1)|))) - ((9 /. 2) * (Real.log |((x_1 - 2))|))) + ((28 /. 3) * (Real.log |((x_1 - 3))|))) + C_1))))))}) := by
  sorry
