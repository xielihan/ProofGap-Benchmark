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

-- exercise: exercise_221_5

theorem proof_gap_exercise_221_5_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) → (((f x_2) - (f x_1)) = ((Real.rpow a x_2) - (Real.rpow a x_1))))))) := by
  sorry

theorem proof_gap_exercise_221_5_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) → (((f x_2) - (f x_1)) = ((Real.rpow a x_2) - (Real.rpow a x_1))))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (0 < a)) ∧ (a < 1)) → (((f x_2) - (f x_1)) < 0))))) := by
  sorry

theorem proof_gap_exercise_221_5_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) → (((f x_2) - (f x_1)) = ((Real.rpow a x_2) - (Real.rpow a x_1))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (0 < a)) ∧ (a < 1)) → (((f x_2) - (f x_1)) < 0))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (a > 1)) → (((f x_2) - (f x_1)) > 0))))) := by
  sorry

theorem proof_gap_exercise_221_5_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) → (((f x_2) - (f x_1)) = ((Real.rpow a x_2) - (Real.rpow a x_1))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (0 < a)) ∧ (a < 1)) → (((f x_2) - (f x_1)) < 0))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (a > 1)) → (((f x_2) - (f x_1)) > 0))))))
  : ((0 < a) ∧ (a < 1)) → (StrictAntiOn f (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_221_5_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) → (((f x_2) - (f x_1)) = ((Real.rpow a x_2) - (Real.rpow a x_1))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (0 < a)) ∧ (a < 1)) → (((f x_2) - (f x_1)) < 0))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (a > 1)) → (((f x_2) - (f x_1)) > 0))))))
  (h7 : ((0 < a) ∧ (a < 1)) → (StrictAntiOn f (Set.univ : Set ℝ)))
  : (a > 1) → (StrictMonoOn f (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_221_5_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) → (((f x_2) - (f x_1)) = ((Real.rpow a x_2) - (Real.rpow a x_1))))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (0 < a)) ∧ (a < 1)) → (((f x_2) - (f x_1)) < 0))))))
  (h6 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_2 > x_1)) ∧ (a > 1)) → (((f x_2) - (f x_1)) > 0))))))
  (h7 : ((0 < a) ∧ (a < 1)) → (StrictAntiOn f (Set.univ : Set ℝ)))
  (h8 : (a > 1) → (StrictMonoOn f (Set.univ : Set ℝ)))
  : (((0 < a) ∧ (a < 1)) → (StrictAntiOn f (Set.univ : Set ℝ))) ∧ ((a > 1) → (StrictMonoOn f (Set.univ : Set ℝ))) := by
  sorry
