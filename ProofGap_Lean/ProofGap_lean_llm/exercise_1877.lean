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

-- exercise: exercise_1877

theorem proof_gap_exercise_1877_1
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))) := by
  sorry

theorem proof_gap_exercise_1877_2
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  : (A + B) = 0 := by
  sorry

theorem proof_gap_exercise_1877_3
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  (h9 : (A + B) = 0)
  : (B + C) = 0 := by
  sorry

theorem proof_gap_exercise_1877_4
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  (h9 : (A + B) = 0)
  (h10 : (B + C) = 0)
  : (A + C) = 1 := by
  sorry

theorem proof_gap_exercise_1877_5
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  (h9 : (A + B) = 0)
  (h10 : (B + C) = 0)
  (h11 : (A + C) = 1)
  : A = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_1877_6
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  (h9 : (A + B) = 0)
  (h10 : (B + C) = 0)
  (h11 : (A + C) = 1)
  (h12 : A = (1 /. 2))
  : B = (-(1 /. 2)) := by
  sorry

theorem proof_gap_exercise_1877_7
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  (h9 : (A + B) = 0)
  (h10 : (B + C) = 0)
  (h11 : (A + C) = 1)
  (h12 : A = (1 /. 2))
  (h13 : B = (-(1 /. 2)))
  : C = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_1877_8
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  (h9 : (A + B) = 0)
  (h10 : (B + C) = 0)
  (h11 : (A + C) = 1)
  (h12 : A = (1 /. 2))
  (h13 : B = (-(1 /. 2)))
  (h14 : C = (1 /. 2))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((1 /. ((x_1 + 1) * ((x_1 ^ (2 : ℕ)) + 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((1 /. (2 * (x_1 + 1))) - ((x_1 - 1) /. (2 * ((x_1 ^ (2 : ℕ)) + 1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_1877_9
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  (h9 : (A + B) = 0)
  (h10 : (B + C) = 0)
  (h11 : (A + C) = 1)
  (h12 : A = (1 /. 2))
  (h13 : B = (-(1 /. 2)))
  (h14 : C = (1 /. 2))
  (h15 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((1 /. ((x_1 + 1) * ((x_1 ^ (2 : ℕ)) + 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((1 /. (2 * (x_1 + 1))) - ((x_1 - 1) /. (2 * ((x_1 ^ (2 : ℕ)) + 1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((1 /. ((x_1 + 1) * ((x_1 ^ (2 : ℕ)) + 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_closed : (ℝ -> ℝ) | forall (x_1 : ℝ), x_1 ∈ (Set.univ : Set ℝ) -> F_closed x_1 = (((((1 /. 2) * (Real.log |(x_1 + 1)|)) - ((1 /. 4) * (Real.log ((x_1 ^ (2 : ℕ)) + 1)))) + ((1 /. 2) * (Real.arctan x_1))) + K)}) := by
  sorry

theorem proof_gap_exercise_1877_10
  (x : ℝ)
  (A : ℝ)
  (B : ℝ)
  (C : ℝ)
  (K : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : A ∈ (Set.univ : Set ℝ))
  (h3 : B ∈ (Set.univ : Set ℝ))
  (h4 : C ∈ (Set.univ : Set ℝ))
  (h5 : K ∈ (Set.univ : Set ℝ))
  (h6 : x ≠ (-(1 : ℝ)))
  (h7 : (1 /. ((x + 1) * ((x ^ (2 : ℕ)) + 1))) = ((A /. (x + 1)) + (((B * x) + C) /. ((x ^ (2 : ℕ)) + 1))))
  (h8 : 1 = ((A * ((x ^ (2 : ℕ)) + 1)) + (((B * x) + C) * (x + 1))))
  (h9 : (A + B) = 0)
  (h10 : (B + C) = 0)
  (h11 : (A + C) = 1)
  (h12 : A = (1 /. 2))
  (h13 : B = (-(1 /. 2)))
  (h14 : C = (1 /. 2))
  (h15 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((1 /. ((x_1 + 1) * ((x_1 ^ (2 : ℕ)) + 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = (((1 /. (2 * (x_1 + 1))) - ((x_1 - 1) /. (2 * ((x_1 ^ (2 : ℕ)) + 1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  (h16 : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((1 /. ((x_1 + 1) * ((x_1 ^ (2 : ℕ)) + 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_closed : (ℝ -> ℝ) | forall (x_1 : ℝ), x_1 ∈ (Set.univ : Set ℝ) -> F_closed x_1 = (((((1 /. 2) * (Real.log |(x_1 + 1)|)) - ((1 /. 4) * (Real.log ((x_1 ^ (2 : ℕ)) + 1)))) + ((1 /. 2) * (Real.arctan x_1))) + K)}))
  : ({F_5 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x_1) = ((1 /. ((x_1 + 1) * ((x_1 ^ (2 : ℕ)) + 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_closed : (ℝ -> ℝ) | forall (x_1 : ℝ), x_1 ∈ (Set.univ : Set ℝ) -> F_closed x_1 = ((((1 /. 4) * (Real.log (((x_1 + 1) ^ (2 : ℕ)) /. ((x_1 ^ (2 : ℕ)) + 1)))) + ((1 /. 2) * (Real.arctan x_1))) + K)}) := by
  sorry
