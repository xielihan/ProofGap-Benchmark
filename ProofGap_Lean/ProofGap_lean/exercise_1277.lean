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

-- exercise: exercise_1277

theorem proof_gap_exercise_1277_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))) := by
  sorry

theorem proof_gap_exercise_1277_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1277_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_1277_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1277_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 0)))) := by
  sorry

theorem proof_gap_exercise_1277_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 0)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1277_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 0)))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → (AntitoneOn y (Set.Ioo 0 1)))) := by
  sorry

theorem proof_gap_exercise_1277_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 0)))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → (AntitoneOn y (Set.Ioo 0 1)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1277_9
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 0)))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → (AntitoneOn y (Set.Ioo 0 1)))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → (MonotoneOn y (Set.Ioi 1)))) := by
  sorry

theorem proof_gap_exercise_1277_10
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((y x) = ((x ^ (2 : ℕ)) - (Real.log (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * (x - 1)) * (x + 1)) /. x)))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < (-(1 : ℝ)))) → (AntitoneOn y (Set.Iio (-(1 : ℝ)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) < x)) ∧ (x < 0)) → (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 0)))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) → (AntitoneOn y (Set.Ioo 0 1)))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (1 < x)) ∧ ((x : EReal) < ⊤)) → (MonotoneOn y (Set.Ioi 1)))))
  : ((((AntitoneOn y (Set.Iio (-(1 : ℝ)))) ∧ (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 0))) ∧ (AntitoneOn y (Set.Ioo 0 1))) ∧ (MonotoneOn y (Set.Ioi 1))) ↔ ((((AntitoneOn y (Set.Iio (-(1 : ℝ)))) ∧ (MonotoneOn y (Set.Ioo (-(1 : ℝ)) 0))) ∧ (AntitoneOn y (Set.Ioo 0 1))) ∧ (MonotoneOn y (Set.Ioi 1))) := by
  sorry
