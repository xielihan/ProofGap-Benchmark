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

-- exercise: exercise_1299

theorem proof_gap_exercise_1299_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((3 * (x ^ (2 : ℕ))) - (x ^ (3 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((6 * x) - (3 * (x ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1299_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((3 * (x ^ (2 : ℕ))) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((6 * x) - (3 * (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (6 - (6 * x))))) := by
  sorry

theorem proof_gap_exercise_1299_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((3 * (x ^ (2 : ℕ))) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((6 * x) - (3 * (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (6 - (6 * x))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1299_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((3 * (x ^ (2 : ℕ))) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((6 * x) - (3 * (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (6 - (6 * x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → (ConcaveOn ℝ (Set.Iio 1) y))) := by
  sorry

theorem proof_gap_exercise_1299_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((3 * (x ^ (2 : ℕ))) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((6 * x) - (3 * (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (6 - (6 * x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → (ConcaveOn ℝ (Set.Iio 1) y))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1299_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((3 * (x ^ (2 : ℕ))) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((6 * x) - (3 * (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (6 - (6 * x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → (ConcaveOn ℝ (Set.Iio 1) y))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → (ConvexOn ℝ (Set.Ioi 1) y))) := by
  sorry

theorem proof_gap_exercise_1299_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((3 * (x ^ (2 : ℕ))) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((6 * x) - (3 * (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (6 - (6 * x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → (ConcaveOn ℝ (Set.Iio 1) y))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → (ConvexOn ℝ (Set.Ioi 1) y))))
  : (y (1 : ℝ)) = 2 := by
  sorry

theorem proof_gap_exercise_1299_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((3 * (x ^ (2 : ℕ))) - (x ^ (3 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = ((6 * x) - (3 * (x ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => y t) x) = (6 - (6 * x))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 1)) → (ConcaveOn ℝ (Set.Iio 1) y))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → (ConvexOn ℝ (Set.Ioi 1) y))))
  (h8 : (y (1 : ℝ)) = 2)
  : (((ConcaveOn ℝ (Set.Iio 1) y) ∧ (ConvexOn ℝ (Set.Ioi 1) y)) ∧ ((1, 2) ∈ ({p | (exists (x : ℝ), p = (x, (y x)) ∧ (x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 2 (fun t => y t) x) = 0))}))) → ((ConcaveOn ℝ (Set.Iio 1) y) ∧ (ConvexOn ℝ (Set.Ioi 1) y)) := by
  sorry
