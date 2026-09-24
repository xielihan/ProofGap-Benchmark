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

-- exercise: exercise_2101

theorem proof_gap_exercise_2101_1
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0))))
  (h5 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ ((x + b) > 0))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.log (x + a)) /. (x + b)) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x) = (((Real.log (x + b)) /. (x + a)) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_5 x) = ((F_3 x) + (F_4 x))))))))}) := by
  sorry

theorem proof_gap_exercise_2101_2
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0))))
  (h5 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ ((x + b) > 0))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.log (x + a)) /. (x + b)) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x) = (((Real.log (x + b)) /. (x + a)) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_5 x) = ((F_3 x) + (F_4 x))))))))}))
  : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)) (F_8 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_7 t) x) = ((Real.log (x + a)) * (iteratedDeriv 1 (fun t => (Real.log (t + b))) x))) ∧ ((iteratedDeriv 1 (fun t => F_8 t) x) = ((Real.log (x + b)) * (iteratedDeriv 1 (fun t => (Real.log (t + a))) x)))) ∧ ((F_9 x) = ((F_7 x) + (F_8 x))))))))}) := by
  sorry

theorem proof_gap_exercise_2101_3
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0))))
  (h5 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ ((x + b) > 0))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.log (x + a)) /. (x + b)) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x) = (((Real.log (x + b)) /. (x + a)) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_5 x) = ((F_3 x) + (F_4 x))))))))}))
  (h7 : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)) (F_8 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_7 t) x) = ((Real.log (x + a)) * (iteratedDeriv 1 (fun t => (Real.log (t + b))) x))) ∧ ((iteratedDeriv 1 (fun t => F_8 t) x) = ((Real.log (x + b)) * (iteratedDeriv 1 (fun t => (Real.log (t + a))) x)))) ∧ ((F_9 x) = ((F_7 x) + (F_8 x))))))))}))
  : ({F_10 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_10 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_15 : (ℝ -> ℝ) | (exists (F_14 : (ℝ -> ℝ)) (F_11 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_11 t) x) = ((Real.log (x + b)) * (iteratedDeriv 1 (fun t => (Real.log (t + a))) x))) ∧ ((iteratedDeriv 1 (fun t => F_14 t) x) = ((Real.log (x + b)) * (iteratedDeriv 1 (fun t => (Real.log (t + a))) x)))) ∧ ((F_15 x) = ((((Real.log (x + a)) * (Real.log (x + b))) - (F_11 x)) + (F_14 x))))))))}) := by
  sorry

theorem proof_gap_exercise_2101_4
  (a : ℝ)
  (b : ℝ)
  (C : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0))))
  (h5 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ ((x + b) > 0))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)) (F_4 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.log (x + a)) /. (x + b)) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((iteratedDeriv 1 (fun t => F_4 t) x) = (((Real.log (x + b)) /. (x + a)) * (iteratedDeriv 1 (fun t => t) x)))) ∧ ((F_5 x) = ((F_3 x) + (F_4 x))))))))}))
  (h7 : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)) (F_8 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_7 t) x) = ((Real.log (x + a)) * (iteratedDeriv 1 (fun t => (Real.log (t + b))) x))) ∧ ((iteratedDeriv 1 (fun t => F_8 t) x) = ((Real.log (x + b)) * (iteratedDeriv 1 (fun t => (Real.log (t + a))) x)))) ∧ ((F_9 x) = ((F_7 x) + (F_8 x))))))))}))
  (h8 : ({F_10 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_10 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_15 : (ℝ -> ℝ) | (exists (F_14 : (ℝ -> ℝ)) (F_11 : (ℝ -> ℝ)), (True ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((((iteratedDeriv 1 (fun t => F_11 t) x) = ((Real.log (x + b)) * (iteratedDeriv 1 (fun t => (Real.log (t + a))) x))) ∧ ((iteratedDeriv 1 (fun t => F_14 t) x) = ((Real.log (x + b)) * (iteratedDeriv 1 (fun t => (Real.log (t + a))) x)))) ∧ ((F_15 x) = ((((Real.log (x + a)) * (Real.log (x + b))) - (F_11 x)) + (F_14 x))))))))}))
  : ({F_16 : (ℝ -> ℝ) | (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((iteratedDeriv 1 (fun t => F_16 t) x) = (((Real.log ((Real.rpow (x + a) (x + a)) * (Real.rpow (x + b) (x + b)))) /. ((x + a) * (x + b))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_17 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((x + a) > 0)) ∧ ((x + b) > 0)) → ((F_17 x) = (((Real.log (x + a)) * (Real.log (x + b))) + C_1))))))}) := by
  sorry
