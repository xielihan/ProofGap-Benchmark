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

-- exercise: exercise_3388_2

theorem proof_gap_exercise_3388_2_1
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, (y_1, z))) = ((((x ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) + (z ^ (2 : ℕ))) - (((3 * x) * y_1) * z))))))
  (h2 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((f (x, (y_1, z))) = ((x * (y_1 ^ (2 : ℕ))) * (z ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (z : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, ((y (x, z)), z))) = 0))))
  (h6 : DifferentiableAt ℝ y (1, 1))
  : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1))) := by
  sorry

theorem proof_gap_exercise_3388_2_2
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, (y_1, z))) = ((((x ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) + (z ^ (2 : ℕ))) - (((3 * x) * y_1) * z))))))
  (h2 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((f (x, (y_1, z))) = ((x * (y_1 ^ (2 : ℕ))) * (z ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (z : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, ((y (x, z)), z))) = 0))))
  (h6 : DifferentiableAt ℝ y (1, 1))
  (h7 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1))))
  : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), (t, (1 : ℝ))))) 1))) := by
  sorry

theorem proof_gap_exercise_3388_2_3
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, (y_1, z))) = ((((x ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) + (z ^ (2 : ℕ))) - (((3 * x) * y_1) * z))))))
  (h2 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((f (x, (y_1, z))) = ((x * (y_1 ^ (2 : ℕ))) * (z ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (z : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, ((y (x, z)), z))) = 0))))
  (h6 : DifferentiableAt ℝ y (1, 1))
  (h7 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1))))
  (h8 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), (t, (1 : ℝ))))) 1))))
  : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3388_2_4
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, (y_1, z))) = ((((x ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) + (z ^ (2 : ℕ))) - (((3 * x) * y_1) * z))))))
  (h2 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((f (x, (y_1, z))) = ((x * (y_1 ^ (2 : ℕ))) * (z ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (z : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, ((y (x, z)), z))) = 0))))
  (h6 : DifferentiableAt ℝ y (1, 1))
  (h7 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1))))
  (h8 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), (t, (1 : ℝ))))) 1))))
  (h9 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-(1 : ℝ)))
  : (iteratedDeriv 1 (fun t => (f (t, ((y (t, (1 : ℝ))), (1 : ℝ))))) 1) = ((iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (1 : ℝ))))) 1) + ((iteratedDeriv 1 (fun t => (f ((1 : ℝ), (t, (1 : ℝ))))) 1) * (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1))) := by
  sorry

theorem proof_gap_exercise_3388_2_5
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, (y_1, z))) = ((((x ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) + (z ^ (2 : ℕ))) - (((3 * x) * y_1) * z))))))
  (h2 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((f (x, (y_1, z))) = ((x * (y_1 ^ (2 : ℕ))) * (z ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (z : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, ((y (x, z)), z))) = 0))))
  (h6 : DifferentiableAt ℝ y (1, 1))
  (h7 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1))))
  (h8 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), (t, (1 : ℝ))))) 1))))
  (h9 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-(1 : ℝ)))
  (h10 : (iteratedDeriv 1 (fun t => (f (t, ((y (t, (1 : ℝ))), (1 : ℝ))))) 1) = ((iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (1 : ℝ))))) 1) + ((iteratedDeriv 1 (fun t => (f ((1 : ℝ), (t, (1 : ℝ))))) 1) * (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1))))
  : (iteratedDeriv 1 (fun t => (f (t, ((y (t, (1 : ℝ))), (1 : ℝ))))) 1) = (1 + (2 * (-(1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3388_2_6
  (F : (ℝ × (ℝ × ℝ) -> ℝ))
  (f : (ℝ × (ℝ × ℝ) -> ℝ))
  (y : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, (y_1, z))) = ((((x ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) + (z ^ (2 : ℕ))) - (((3 * x) * y_1) * z))))))
  (h2 : (forall (x : ℝ) (y_1 : ℝ) (z : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y_1 ∈ (Set.univ : Set ℝ))) ∧ (z ∈ (Set.univ : Set ℝ))) → ((f (x, (y_1, z))) = ((x * (y_1 ^ (2 : ℕ))) * (z ^ (3 : ℕ)))))))
  (h3 : (F ((1 : ℝ), ((1 : ℝ), (1 : ℝ)))) = 0)
  (h4 : (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1) ≠ 0)
  (h5 : (forall (x : ℝ) (z : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (z ∈ (Set.univ : Set ℝ))) → ((F (x, ((y (x, z)), z))) = 0))))
  (h6 : DifferentiableAt ℝ y (1, 1))
  (h7 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => F (t, ((1 : ℝ), (1 : ℝ)))) 1) /. (iteratedDeriv 1 (fun t => F ((1 : ℝ), (t, (1 : ℝ)))) 1))))
  (h8 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-((iteratedDeriv 1 (fun t => (F (t, ((1 : ℝ), (1 : ℝ))))) 1) /. (iteratedDeriv 1 (fun t => (F ((1 : ℝ), (t, (1 : ℝ))))) 1))))
  (h9 : (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1) = (-(1 : ℝ)))
  (h10 : (iteratedDeriv 1 (fun t => (f (t, ((y (t, (1 : ℝ))), (1 : ℝ))))) 1) = ((iteratedDeriv 1 (fun t => (f (t, ((1 : ℝ), (1 : ℝ))))) 1) + ((iteratedDeriv 1 (fun t => (f ((1 : ℝ), (t, (1 : ℝ))))) 1) * (iteratedDeriv 1 (fun t => y (t, (1 : ℝ))) 1))))
  (h11 : (iteratedDeriv 1 (fun t => (f (t, ((y (t, (1 : ℝ))), (1 : ℝ))))) 1) = (1 + (2 * (-(1 : ℝ)))))
  : (iteratedDeriv 1 (fun t => (f (t, ((y (t, (1 : ℝ))), (1 : ℝ))))) 1) = (-(1 : ℝ)) := by
  sorry
