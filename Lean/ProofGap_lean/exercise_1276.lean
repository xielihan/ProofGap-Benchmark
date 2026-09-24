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

-- exercise: exercise_1276

theorem proof_gap_exercise_1276_1
  (y : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : n > 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → ((y x) = ((Real.rpow x n) * (Real.exp (-x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((Real.rpow x (n - 1)) * (Real.exp (-x))) * (n - x))))) := by
  sorry

theorem proof_gap_exercise_1276_2
  (y : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : n > 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → ((y x) = ((Real.rpow x n) * (Real.exp (-x)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((Real.rpow x (n - 1)) * (Real.exp (-x))) * (n - x))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1276_3
  (y : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : n > 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → ((y x) = ((Real.rpow x n) * (Real.exp (-x)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((Real.rpow x (n - 1)) * (Real.exp (-x))) * (n - x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → (MonotoneOn y (Set.Ioo 0 n)))) := by
  sorry

theorem proof_gap_exercise_1276_4
  (y : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : n > 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → ((y x) = ((Real.rpow x n) * (Real.exp (-x)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((Real.rpow x (n - 1)) * (Real.exp (-x))) * (n - x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → (MonotoneOn y (Set.Ioo 0 n)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi n))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1276_5
  (y : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : n > 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → ((y x) = ((Real.rpow x n) * (Real.exp (-x)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((Real.rpow x (n - 1)) * (Real.exp (-x))) * (n - x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → (MonotoneOn y (Set.Ioo 0 n)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi n))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi n))) → (AntitoneOn y (Set.Ioi n)))) := by
  sorry

theorem proof_gap_exercise_1276_6
  (y : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : n > 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 0)) → ((y x) = ((Real.rpow x n) * (Real.exp (-x)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((Real.rpow x (n - 1)) * (Real.exp (-x))) * (n - x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 n))) → (MonotoneOn y (Set.Ioo 0 n)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi n))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi n))) → (AntitoneOn y (Set.Ioi n)))))
  : ((MonotoneOn y (Set.Ioo 0 n)) ∧ (AntitoneOn y (Set.Ioi n))) ↔ ((MonotoneOn y (Set.Ioo 0 n)) ∧ (AntitoneOn y (Set.Ioi n))) := by
  sorry
