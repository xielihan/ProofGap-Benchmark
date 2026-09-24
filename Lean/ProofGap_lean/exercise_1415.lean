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

-- exercise: exercise_1415

theorem proof_gap_exercise_1415_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x - 1) ^ (3 : ℕ))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (3 * ((x - 1) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1415_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x - 1) ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (3 * ((x - 1) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1415_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x - 1) ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (3 * ((x - 1) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : Monotone y := by
  sorry

theorem proof_gap_exercise_1415_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x - 1) ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (3 * ((x - 1) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h4 : Monotone y)
  : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (lpMaximumPoints y)))) := by
  sorry

theorem proof_gap_exercise_1415_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x - 1) ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (3 * ((x - 1) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h4 : Monotone y)
  (h5 : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (lpMaximumPoints y)))))
  : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (lpMinimumPoints y)))) := by
  sorry

theorem proof_gap_exercise_1415_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x - 1) ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (3 * ((x - 1) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h4 : Monotone y)
  (h5 : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (lpMaximumPoints y)))))
  (h6 : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (lpMinimumPoints y)))))
  : (lpMaximumPoints y) = ∅ := by
  sorry

theorem proof_gap_exercise_1415_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x - 1) ^ (3 : ℕ))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (3 * ((x - 1) ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h4 : Monotone y)
  (h5 : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (lpMaximumPoints y)))))
  (h6 : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (lpMinimumPoints y)))))
  (h7 : (lpMaximumPoints y) = ∅)
  : (lpMinimumPoints y) = ∅ := by
  sorry
