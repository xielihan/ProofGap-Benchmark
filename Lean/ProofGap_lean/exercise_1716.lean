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

-- exercise: exercise_1716

theorem proof_gap_exercise_1716_1
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (1 - (x ^ (2 : ℕ))) ≠ 0)
  (h4 : ((1 + x) /. (1 - x)) > 0)
  : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((1 - (x_1 ^ (2 : ℕ))) ≠ 0)) ∧ (((1 + x_1) /. (1 - x_1)) > 0)) → (((1 /. (1 - (x_1 ^ (2 : ℕ)))) • (fderiv ℝ (fun (x_2 : ℝ) => x_2))) = ((1 /. 2) • (fderiv ℝ (fun (x_2 : ℝ) => (Real.log ((1 + x_2) /. (1 - x_2))))))))) := by
  sorry

theorem proof_gap_exercise_1716_2
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (1 - (x ^ (2 : ℕ))) ≠ 0)
  (h4 : ((1 + x) /. (1 - x)) > 0)
  (h5 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((1 - (x_1 ^ (2 : ℕ))) ≠ 0)) ∧ (((1 + x_1) /. (1 - x_1)) > 0)) → (((1 /. (1 - (x_1 ^ (2 : ℕ)))) • (fderiv ℝ (fun (x_2 : ℝ) => x_2))) = ((1 /. 2) • (fderiv ℝ (fun (x_2 : ℝ) => (Real.log ((1 + x_2) /. (1 - x_2))))))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((1 /. (1 - (x_1 ^ (2 : ℕ)))) * (Real.log ((1 + x_1) /. (1 - x_1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.log ((1 + x_1) /. (1 - x_1))) * (iteratedDeriv 1 (fun t => (Real.log ((1 + t) /. (1 - t)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}) := by
  sorry

theorem proof_gap_exercise_1716_3
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (1 - (x ^ (2 : ℕ))) ≠ 0)
  (h4 : ((1 + x) /. (1 - x)) > 0)
  (h5 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((1 - (x_1 ^ (2 : ℕ))) ≠ 0)) ∧ (((1 + x_1) /. (1 - x_1)) > 0)) → (((1 /. (1 - (x_1 ^ (2 : ℕ)))) • (fderiv ℝ (fun (x_2 : ℝ) => x_2))) = ((1 /. 2) • (fderiv ℝ (fun (x_2 : ℝ) => (Real.log ((1 + x_2) /. (1 - x_2))))))))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((1 /. (1 - (x_1 ^ (2 : ℕ)))) * (Real.log ((1 + x_1) /. (1 - x_1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.log ((1 + x_1) /. (1 - x_1))) * (iteratedDeriv 1 (fun t => (Real.log ((1 + t) /. (1 - t)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}))
  : ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.log ((1 + x_1) /. (1 - x_1))) * (iteratedDeriv 1 (fun t => (Real.log ((1 + t) /. (1 - t)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_5 x_1) = (((1 /. 4) * ((Real.log ((1 + x_1) /. (1 - x_1))) ^ (2 : ℕ))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1716_4
  (C : ℝ)
  (x : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (1 - (x ^ (2 : ℕ))) ≠ 0)
  (h4 : ((1 + x) /. (1 - x)) > 0)
  (h5 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((1 - (x_1 ^ (2 : ℕ))) ≠ 0)) ∧ (((1 + x_1) /. (1 - x_1)) > 0)) → (((1 /. (1 - (x_1 ^ (2 : ℕ)))) • (fderiv ℝ (fun (x_2 : ℝ) => x_2))) = ((1 /. 2) • (fderiv ℝ (fun (x_2 : ℝ) => (Real.log ((1 + x_2) /. (1 - x_2))))))))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((1 /. (1 - (x_1 ^ (2 : ℕ)))) * (Real.log ((1 + x_1) /. (1 - x_1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.log ((1 + x_1) /. (1 - x_1))) * (iteratedDeriv 1 (fun t => (Real.log ((1 + t) /. (1 - t)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}))
  (h7 : ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_3 t) x_1) = ((Real.log ((1 + x_1) /. (1 - x_1))) * (iteratedDeriv 1 (fun t => (Real.log ((1 + t) /. (1 - t)))) x_1))) ∧ ((F_4 x_1) = ((1 /. 2) * (F_3 x_1)))))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_5 x_1) = (((1 /. 4) * ((Real.log ((1 + x_1) /. (1 - x_1))) ^ (2 : ℕ))) + C_1))))))}))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x_1) = (((1 /. (1 - (x_1 ^ (2 : ℕ)))) * (Real.log ((1 + x_1) /. (1 - x_1)))) * (iteratedDeriv 1 (fun t => t) x_1)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_5 x_1) = (((1 /. 4) * ((Real.log ((1 + x_1) /. (1 - x_1))) ^ (2 : ℕ))) + C_1))))))}) := by
  sorry
