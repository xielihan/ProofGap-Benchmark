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

-- exercise: exercise_1870

theorem proof_gap_exercise_1870_1
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  : ((x ^ (4 : ℕ)) /. (((x ^ (4 : ℕ)) + (5 * (x ^ (2 : ℕ)))) + 4)) = (1 + ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4)))) := by
  sorry

theorem proof_gap_exercise_1870_2
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((x ^ (4 : ℕ)) /. (((x ^ (4 : ℕ)) + (5 * (x ^ (2 : ℕ)))) + 4)) = (1 + ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4)))))
  (h4 : A_1 = 0)
  (h5 : B_1 = (1 /. 3))
  (h6 : A_2 = 0)
  (h7 : B_2 = (-(16 /. 3)))
  : ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4))) = ((((A_1 * x) + B_1) /. ((x ^ (2 : ℕ)) + 1)) + (((A_2 * x) + B_2) /. ((x ^ (2 : ℕ)) + 4))) := by
  sorry

theorem proof_gap_exercise_1870_3
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((x ^ (4 : ℕ)) /. (((x ^ (4 : ℕ)) + (5 * (x ^ (2 : ℕ)))) + 4)) = (1 + ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4)))))
  (h4 : A_1 = 0)
  (h5 : B_1 = (1 /. 3))
  (h6 : A_2 = 0)
  (h7 : B_2 = (-(16 /. 3)))
  (h8 : ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4))) = ((((A_1 * x) + B_1) /. ((x ^ (2 : ℕ)) + 1)) + (((A_2 * x) + B_2) /. ((x ^ (2 : ℕ)) + 4))))
  : ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4))) = ((1 /. (3 * ((x ^ (2 : ℕ)) + 1))) - (16 /. (3 * ((x ^ (2 : ℕ)) + 4)))) := by
  sorry

theorem proof_gap_exercise_1870_4
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((x ^ (4 : ℕ)) /. (((x ^ (4 : ℕ)) + (5 * (x ^ (2 : ℕ)))) + 4)) = (1 + ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4)))))
  (h4 : A_1 = 0)
  (h5 : B_1 = (1 /. 3))
  (h6 : A_2 = 0)
  (h7 : B_2 = (-(16 /. 3)))
  (h8 : ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4))) = ((((A_1 * x) + B_1) /. ((x ^ (2 : ℕ)) + 1)) + (((A_2 * x) + B_2) /. ((x ^ (2 : ℕ)) + 4))))
  (h9 : ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4))) = ((1 /. (3 * ((x ^ (2 : ℕ)) + 1))) - (16 /. (3 * ((x ^ (2 : ℕ)) + 4)))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (4 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + (5 * (x_1 ^ (2 : ℕ)))) + 4)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((1 + (1 /. (3 * ((x_1 ^ (2 : ℕ)) + 1)))) - (16 /. (3 * ((x_1 ^ (2 : ℕ)) + 4)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_1870_5
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((x ^ (4 : ℕ)) /. (((x ^ (4 : ℕ)) + (5 * (x ^ (2 : ℕ)))) + 4)) = (1 + ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4)))))
  (h4 : A_1 = 0)
  (h5 : B_1 = (1 /. 3))
  (h6 : A_2 = 0)
  (h7 : B_2 = (-(16 /. 3)))
  (h8 : ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4))) = ((((A_1 * x) + B_1) /. ((x ^ (2 : ℕ)) + 1)) + (((A_2 * x) + B_2) /. ((x ^ (2 : ℕ)) + 4))))
  (h9 : ((-((5 * (x ^ (2 : ℕ))) + 4)) /. (((x ^ (2 : ℕ)) + 1) * ((x ^ (2 : ℕ)) + 4))) = ((1 /. (3 * ((x ^ (2 : ℕ)) + 1))) - (16 /. (3 * ((x ^ (2 : ℕ)) + 4)))))
  (h10 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (4 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + (5 * (x_1 ^ (2 : ℕ)))) + 4)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((1 + (1 /. (3 * ((x_1 ^ (2 : ℕ)) + 1)))) - (16 /. (3 * ((x_1 ^ (2 : ℕ)) + 4)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((x_1 ^ (4 : ℕ)) /. (((x_1 ^ (4 : ℕ)) + (5 * (x_1 ^ (2 : ℕ)))) + 4)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_5 x_1) = (((x_1 + ((1 /. 3) * (Real.arctan x_1))) - ((8 /. 3) * (Real.arctan (x_1 /. 2)))) + C_1))))))}) := by
  sorry
