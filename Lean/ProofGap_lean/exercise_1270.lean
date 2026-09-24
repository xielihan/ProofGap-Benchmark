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

-- exercise: exercise_1270

theorem proof_gap_exercise_1270_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (1 - x)) * (1 + x)) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1270_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (1 - x)) * (1 + x)) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1270_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (1 - x)) * (1 + x)) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_1270_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (1 - x)) * (1 + x)) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1270_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (1 - x)) * (1 + x)) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 1)))) := by
  sorry

theorem proof_gap_exercise_1270_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (1 - x)) * (1 + x)) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 1)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1270_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (1 - x)) * (1 + x)) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 1)))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → (AntitoneOn y (Set.Ioi 1)))) := by
  sorry

theorem proof_gap_exercise_1270_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 * x) /. (1 + (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (1 - x)) * (1 + x)) /. ((1 + (x ^ (2 : ℕ))) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 1)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 1)))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → (AntitoneOn y (Set.Ioi 1)))))
  : (((AntitoneOn y (Set.Iio (-(1 : ℝ)))) ∧ (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 1))) ∧ (AntitoneOn y (Set.Ioi 1))) ↔ (((MonotoneOn y (Set.Ioo (-(1 : ℝ)) 1)) ∧ (AntitoneOn y (Set.Iio (-(1 : ℝ))))) ∧ (AntitoneOn y (Set.Ioi 1))) := by
  sorry
