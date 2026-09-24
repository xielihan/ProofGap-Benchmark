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

-- exercise: exercise_1872

theorem proof_gap_exercise_1872_1
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))) := by
  sorry

theorem proof_gap_exercise_1872_2
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_1872_3
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  (h6 : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))))
  : 2 = ((-(2 : ℝ)) * B) := by
  sorry

theorem proof_gap_exercise_1872_4
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  (h6 : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))))
  (h7 : 2 = ((-(2 : ℝ)) * B))
  : B = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_1872_5
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  (h6 : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))))
  (h7 : 2 = ((-(2 : ℝ)) * B))
  (h8 : B = (-(1 : ℝ)))
  : 2 = (4 * C_1) := by
  sorry

theorem proof_gap_exercise_1872_6
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  (h6 : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))))
  (h7 : 2 = ((-(2 : ℝ)) * B))
  (h8 : B = (-(1 : ℝ)))
  (h9 : 2 = (4 * C_1))
  : C_1 = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_1872_7
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  (h6 : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))))
  (h7 : 2 = ((-(2 : ℝ)) * B))
  (h8 : B = (-(1 : ℝ)))
  (h9 : 2 = (4 * C_1))
  (h10 : C_1 = (1 /. 2))
  : (A + C_1) = 1 := by
  sorry

theorem proof_gap_exercise_1872_8
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  (h6 : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))))
  (h7 : 2 = ((-(2 : ℝ)) * B))
  (h8 : B = (-(1 : ℝ)))
  (h9 : 2 = (4 * C_1))
  (h10 : C_1 = (1 /. 2))
  (h11 : (A + C_1) = 1)
  : A = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_1872_9
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  (h6 : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))))
  (h7 : 2 = ((-(2 : ℝ)) * B))
  (h8 : B = (-(1 : ℝ)))
  (h9 : 2 = (4 * C_1))
  (h10 : C_1 = (1 /. 2))
  (h11 : (A + C_1) = 1)
  (h12 : A = (1 /. 2))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (((x_1 + 1) ^ (2 : ℕ)) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 /. (2 * (x_1 + 1))) - (1 /. ((x_1 + 1) ^ (2 : ℕ)))) + (1 /. (2 * (x_1 - 1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) := by
  sorry

theorem proof_gap_exercise_1872_10
  (x : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) ∧ (x ≠ 1))
  (h2 : A = (1 /. 2))
  (h3 : B = (-(1 : ℝ)))
  (h4 : C_1 = (1 /. 2))
  (h5 : (((x ^ (2 : ℕ)) + 1) /. (((x + 1) ^ (2 : ℕ)) * (x - 1))) = (((A /. (x + 1)) + (B /. ((x + 1) ^ (2 : ℕ)))) + (C_1 /. (x - 1))))
  (h6 : ((x ^ (2 : ℕ)) + 1) = ((((A * (x + 1)) * (x - 1)) + (B * (x - 1))) + (C_1 * ((x + 1) ^ (2 : ℕ)))))
  (h7 : 2 = ((-(2 : ℝ)) * B))
  (h8 : B = (-(1 : ℝ)))
  (h9 : 2 = (4 * C_1))
  (h10 : C_1 = (1 /. 2))
  (h11 : (A + C_1) = 1)
  (h12 : A = (1 /. 2))
  (h13 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (((x_1 + 1) ^ (2 : ℕ)) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((((1 /. (2 * (x_1 + 1))) - (1 /. ((x_1 + 1) ^ (2 : ℕ)))) + (1 /. (2 * (x_1 - 1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ 1)) → ((iteratedDeriv 1 (fun t => F_4 t) x_1) = ((((x_1 ^ (2 : ℕ)) + 1) /. (((x_1 + 1) ^ (2 : ℕ)) * (x_1 - 1))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) ∧ (x_1 ≠ 1)) → ((F_5 x_1) = ((((1 /. 2) * (Real.log |(((x_1 ^ (2 : ℕ)) - 1))|)) + (1 /. (x_1 + 1))) + C))))))}) := by
  sorry
