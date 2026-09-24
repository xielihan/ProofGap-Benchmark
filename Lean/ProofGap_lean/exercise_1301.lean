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

-- exercise: exercise_1301

theorem proof_gap_exercise_1301_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.rpow x (5 /. 3)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + ((5 /. 3) * (Real.rpow x (2 /. 3))))))) := by
  sorry

theorem proof_gap_exercise_1301_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.rpow x (5 /. 3)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + ((5 /. 3) * (Real.rpow x (2 /. 3))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = ((10 /. 9) * (Real.rpow x (-(1 /. 3))))))) := by
  sorry

theorem proof_gap_exercise_1301_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.rpow x (5 /. 3)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + ((5 /. 3) * (Real.rpow x (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = ((10 /. 9) * (Real.rpow x (-(1 /. 3))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1301_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.rpow x (5 /. 3)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + ((5 /. 3) * (Real.rpow x (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = ((10 /. 9) * (Real.rpow x (-(1 /. 3))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → (ConvexOn ℝ (Set.Iio 0) y))) := by
  sorry

theorem proof_gap_exercise_1301_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.rpow x (5 /. 3)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + ((5 /. 3) * (Real.rpow x (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = ((10 /. 9) * (Real.rpow x (-(1 /. 3))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → (ConcaveOn ℝ (Set.Iio 0) y))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1301_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.rpow x (5 /. 3)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + ((5 /. 3) * (Real.rpow x (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = ((10 /. 9) * (Real.rpow x (-(1 /. 3))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → (ConvexOn ℝ (Set.Iio 0) y))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ ((x : EReal) < ⊤)) → (ConcaveOn ℝ (Set.Ioi 0) y))) := by
  sorry

theorem proof_gap_exercise_1301_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.rpow x (5 /. 3)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + ((5 /. 3) * (Real.rpow x (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = ((10 /. 9) * (Real.rpow x (-(1 /. 3))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → (ConcaveOn ℝ (Set.Iio 0) y))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ ((x : EReal) < ⊤)) → (ConvexOn ℝ (Set.Ioi 0) y))))
  : Not (DifferentiableAt ℝ (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => y t) x1)) 0) := by
  sorry

theorem proof_gap_exercise_1301_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = (x + (Real.rpow x (5 /. 3)))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (1 + ((5 /. 3) * (Real.rpow x (2 /. 3))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 2 (fun t => y t) x) = ((10 /. 9) * (Real.rpow x (-(1 /. 3))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → ((iteratedDeriv 2 (fun t => y t) x) < 0))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (⊥ < (x : EReal))) ∧ (x < 0)) → (ConvexOn ℝ (Set.Iio 0) y))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ ((x : EReal) < ⊤)) → ((iteratedDeriv 2 (fun t => y t) x) > 0))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ ((x : EReal) < ⊤)) → (ConcaveOn ℝ (Set.Ioi 0) y))))
  (h8 : Not (DifferentiableAt ℝ (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => y t) x1)) 0))
  : (((ConvexOn ℝ (Set.Iio 0) y) ∧ (ConcaveOn ℝ (Set.Ioi 0) y)) ∧ ((0, (y (0 : ℝ))) = (0, 0))) ↔ ((ConvexOn ℝ (Set.Iio 0) y) ∧ (ConcaveOn ℝ (Set.Ioi 0) y)) := by
  sorry
