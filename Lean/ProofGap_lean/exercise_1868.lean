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

-- exercise: exercise_1868

theorem proof_gap_exercise_1868_1
  (x : ℝ)
  (C : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (x ≠ 1))
  (h2 : C ∈ (Set.univ : Set ℝ))
  : ((x ^ (10 : ℕ)) /. (((x ^ (2 : ℕ)) + x) - 2)) = ((((((((((x ^ (8 : ℕ)) - (x ^ (7 : ℕ))) + (3 * (x ^ (6 : ℕ)))) - (5 * (x ^ (5 : ℕ)))) + (11 * (x ^ (4 : ℕ)))) - (21 * (x ^ (3 : ℕ)))) + (43 * (x ^ (2 : ℕ)))) - (85 * x)) + 171) + ((((-(341 : ℝ)) * x) + 342) /. (((x ^ (2 : ℕ)) + x) - 2))) := by
  sorry

theorem proof_gap_exercise_1868_2
  (x : ℝ)
  (C : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (x ≠ 1))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((x ^ (10 : ℕ)) /. (((x ^ (2 : ℕ)) + x) - 2)) = ((((((((((x ^ (8 : ℕ)) - (x ^ (7 : ℕ))) + (3 * (x ^ (6 : ℕ)))) - (5 * (x ^ (5 : ℕ)))) + (11 * (x ^ (4 : ℕ)))) - (21 * (x ^ (3 : ℕ)))) + (43 * (x ^ (2 : ℕ)))) - (85 * x)) + 171) + ((((-(341 : ℝ)) * x) + 342) /. (((x ^ (2 : ℕ)) + x) - 2))))
  (h4 : A = (-(1024 /. 3)))
  (h5 : B = (1 /. 3))
  : ((((-(341 : ℝ)) * x) + 342) /. (((x ^ (2 : ℕ)) + x) - 2)) = ((A /. (x + 2)) + (B /. (x - 1))) := by
  sorry

theorem proof_gap_exercise_1868_3
  (x : ℝ)
  (C : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (x ≠ 1))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((x ^ (10 : ℕ)) /. (((x ^ (2 : ℕ)) + x) - 2)) = ((((((((((x ^ (8 : ℕ)) - (x ^ (7 : ℕ))) + (3 * (x ^ (6 : ℕ)))) - (5 * (x ^ (5 : ℕ)))) + (11 * (x ^ (4 : ℕ)))) - (21 * (x ^ (3 : ℕ)))) + (43 * (x ^ (2 : ℕ)))) - (85 * x)) + 171) + ((((-(341 : ℝ)) * x) + 342) /. (((x ^ (2 : ℕ)) + x) - 2))))
  (h4 : A = (-(1024 /. 3)))
  (h5 : B = (1 /. 3))
  (h6 : ((((-(341 : ℝ)) * x) + 342) /. (((x ^ (2 : ℕ)) + x) - 2)) = ((A /. (x + 2)) + (B /. (x - 1))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (10 : ℕ)) /. (((x_1 ^ (2 : ℕ)) + x_1) - 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((((((((((x_1 ^ (8 : ℕ)) - (x_1 ^ (7 : ℕ))) + (3 * (x_1 ^ (6 : ℕ)))) - (5 * (x_1 ^ (5 : ℕ)))) + (11 * (x_1 ^ (4 : ℕ)))) - (21 * (x_1 ^ (3 : ℕ)))) + (43 * (x_1 ^ (2 : ℕ)))) - (85 * x_1)) + 171) - (1024 /. (3 * (x_1 + 2)))) + (1 /. (3 * (x_1 - 1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_1868_4
  (x : ℝ)
  (C : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(2 : ℝ)))) ∧ (x ≠ 1))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : ((x ^ (10 : ℕ)) /. (((x ^ (2 : ℕ)) + x) - 2)) = ((((((((((x ^ (8 : ℕ)) - (x ^ (7 : ℕ))) + (3 * (x ^ (6 : ℕ)))) - (5 * (x ^ (5 : ℕ)))) + (11 * (x ^ (4 : ℕ)))) - (21 * (x ^ (3 : ℕ)))) + (43 * (x ^ (2 : ℕ)))) - (85 * x)) + 171) + ((((-(341 : ℝ)) * x) + 342) /. (((x ^ (2 : ℕ)) + x) - 2))))
  (h4 : A = (-(1024 /. 3)))
  (h5 : B = (1 /. 3))
  (h6 : ((((-(341 : ℝ)) * x) + 342) /. (((x ^ (2 : ℕ)) + x) - 2)) = ((A /. (x + 2)) + (B /. (x - 1))))
  (h7 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((x_1 ^ (10 : ℕ)) /. (((x_1 ^ (2 : ℕ)) + x_1) - 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((((((((((x_1 ^ (8 : ℕ)) - (x_1 ^ (7 : ℕ))) + (3 * (x_1 ^ (6 : ℕ)))) - (5 * (x_1 ^ (5 : ℕ)))) + (11 * (x_1 ^ (4 : ℕ)))) - (21 * (x_1 ^ (3 : ℕ)))) + (43 * (x_1 ^ (2 : ℕ)))) - (85 * x_1)) + 171) - (1024 /. (3 * (x_1 + 2)))) + (1 /. (3 * (x_1 - 1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = (((x_1 ^ (10 : ℕ)) /. (((x_1 ^ (2 : ℕ)) + x_1) - 2)) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(2 : ℝ)))) ∧ (x_1 ≠ 1)) → ((F_5 x_1) = ((((((((((((x_1 ^ (9 : ℕ)) /. 9) - ((x_1 ^ (8 : ℕ)) /. 8)) + ((3 * (x_1 ^ (7 : ℕ))) /. 7)) - ((5 * (x_1 ^ (6 : ℕ))) /. 6)) + ((11 * (x_1 ^ (5 : ℕ))) /. 5)) - ((21 * (x_1 ^ (4 : ℕ))) /. 4)) + ((43 * (x_1 ^ (3 : ℕ))) /. 3)) - ((85 * (x_1 ^ (2 : ℕ))) /. 2)) + (171 * x_1)) + ((1 /. 3) * (Real.log |(((x_1 - 1) /. ((x_1 + 2) ^ (1024 : ℕ))))|))) + C_1))))))}) := by
  sorry
