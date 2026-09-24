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

-- exercise: exercise_1268

theorem proof_gap_exercise_1268_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 + x) - (x ^ (2 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 - (2 * x))))) := by
  sorry

theorem proof_gap_exercise_1268_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 + x) - (x ^ (2 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 - (2 * x))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1268_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 + x) - (x ^ (2 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 - (2 * x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → (StrictMonoOn y (Set.Iio (1 /. 2))))) := by
  sorry

theorem proof_gap_exercise_1268_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 + x) - (x ^ (2 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 - (2 * x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → (StrictMonoOn y (Set.Iio (1 /. 2))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1268_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 + x) - (x ^ (2 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 - (2 * x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → (StrictMonoOn y (Set.Iio (1 /. 2))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ ((x : EReal) < ⊤)) → (StrictAntiOn y (Set.Ioi (1 /. 2))))) := by
  sorry

theorem proof_gap_exercise_1268_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 + x) - (x ^ (2 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 - (2 * x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → (StrictMonoOn y (Set.Iio (1 /. 2))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ ((x : EReal) < ⊤)) → (StrictAntiOn y (Set.Ioi (1 /. 2))))))
  : StrictMonoOn y (Set.Iio (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_1268_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((2 + x) - (x ^ (2 : ℕ)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 - (2 * x))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (1 /. 2))) → (StrictMonoOn y (Set.Iio (1 /. 2))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((1 /. 2) < x)) ∧ ((x : EReal) < ⊤)) → (StrictAntiOn y (Set.Ioi (1 /. 2))))))
  (h7 : StrictMonoOn y (Set.Iio (1 /. 2)))
  : StrictAntiOn y (Set.Ioi (1 /. 2)) := by
  sorry
