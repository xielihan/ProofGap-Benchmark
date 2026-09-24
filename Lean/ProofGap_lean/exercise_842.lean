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

-- exercise: exercise_842

theorem proof_gap_exercise_842_1
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = (((1 - x_1) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ))) - ((((4 * x_1) * (1 - x_1)) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))) - ((((9 * (x_1 ^ (2 : ℕ))) * (1 - x_1)) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_842_2
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = (((1 - x_1) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ))) - ((((4 * x_1) * (1 - x_1)) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))) - ((((9 * (x_1 ^ (2 : ℕ))) * (1 - x_1)) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - x_1) ^ (2 : ℕ))) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))) * (((1 + (6 * x_1)) + (15 * (x_1 ^ (2 : ℕ)))) + (14 * (x_1 ^ (3 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_842_3
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = (((1 - x_1) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ))) - ((((4 * x_1) * (1 - x_1)) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))) - ((((9 * (x_1 ^ (2 : ℕ))) * (1 - x_1)) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - x_1) ^ (2 : ℕ))) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))) * (((1 + (6 * x_1)) + (15 * (x_1 ^ (2 : ℕ)))) + (14 * (x_1 ^ (3 : ℕ)))))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((((-((1 - x_1) ^ (5 : ℕ))) * (1 + x_1)) * (1 + (2 * x_1))) * ((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ))))) * (((1 + x_1) + (x_1 ^ (2 : ℕ))) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_842_4
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = (((1 - x_1) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ))) - ((((4 * x_1) * (1 - x_1)) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))) - ((((9 * (x_1 ^ (2 : ℕ))) * (1 - x_1)) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - x_1) ^ (2 : ℕ))) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))) * (((1 + (6 * x_1)) + (15 * (x_1 ^ (2 : ℕ)))) + (14 * (x_1 ^ (3 : ℕ)))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((((-((1 - x_1) ^ (5 : ℕ))) * (1 + x_1)) * (1 + (2 * x_1))) * ((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ))))) * (((1 + x_1) + (x_1 ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x_1) = 0) ↔ (((((x_1 = 1) ∨ (x_1 = (-(1 : ℝ)))) ∨ (x_1 = (-(1 /. 2)))) ∨ (((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ)))) = 0)) ∨ (((1 + x_1) + (x_1 ^ (2 : ℕ))) = 0))))) := by
  sorry

theorem proof_gap_exercise_842_5
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = (((1 - x_1) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ))) - ((((4 * x_1) * (1 - x_1)) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))) - ((((9 * (x_1 ^ (2 : ℕ))) * (1 - x_1)) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - x_1) ^ (2 : ℕ))) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))) * (((1 + (6 * x_1)) + (15 * (x_1 ^ (2 : ℕ)))) + (14 * (x_1 ^ (3 : ℕ)))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((((-((1 - x_1) ^ (5 : ℕ))) * (1 + x_1)) * (1 + (2 * x_1))) * ((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ))))) * (((1 + x_1) + (x_1 ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x_1) = 0) ↔ (((((x_1 = 1) ∨ (x_1 = (-(1 : ℝ)))) ∨ (x_1 = (-(1 /. 2)))) ∨ (((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ)))) = 0)) ∨ (((1 + x_1) + (x_1 ^ (2 : ℕ))) = 0))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((Not (((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ)))) = 0)) ∧ (Not (((1 + x_1) + (x_1 ^ (2 : ℕ))) = 0))))) := by
  sorry

theorem proof_gap_exercise_842_6
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = (((1 - x_1) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ))) - ((((4 * x_1) * (1 - x_1)) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (3 : ℕ)))) - ((((9 * (x_1 ^ (2 : ℕ))) * (1 - x_1)) * ((1 - (x_1 ^ (2 : ℕ))) ^ (2 : ℕ))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = ((((-((1 - x_1) ^ (2 : ℕ))) * (1 - (x_1 ^ (2 : ℕ)))) * ((1 - (x_1 ^ (3 : ℕ))) ^ (2 : ℕ))) * (((1 + (6 * x_1)) + (15 * (x_1 ^ (2 : ℕ)))) + (14 * (x_1 ^ (3 : ℕ)))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((((-((1 - x_1) ^ (5 : ℕ))) * (1 + x_1)) * (1 + (2 * x_1))) * ((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ))))) * (((1 + x_1) + (x_1 ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x_1) = 0) ↔ (((((x_1 = 1) ∨ (x_1 = (-(1 : ℝ)))) ∨ (x_1 = (-(1 /. 2)))) ∨ (((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ)))) = 0)) ∨ (((1 + x_1) + (x_1 ^ (2 : ℕ))) = 0))))))
  (h7 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((Not (((1 + (4 * x_1)) + (7 * (x_1 ^ (2 : ℕ)))) = 0)) ∧ (Not (((1 + x_1) + (x_1 ^ (2 : ℕ))) = 0))))))
  : (x ∈ ({x | x = 1 ∨ x = (-(1 : ℝ)) ∨ x = (-(1 /. 2))})) ↔ ((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x) = 0)) := by
  sorry
