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

-- exercise: exercise_2115

theorem proof_gap_exercise_2115_1
  : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))) := by
  sorry

theorem proof_gap_exercise_2115_2
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (2 : ℕ))) > 0))) := by
  sorry

theorem proof_gap_exercise_2115_3
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (2 : ℕ))) > 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) > 0))) := by
  sorry

theorem proof_gap_exercise_2115_4
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (2 : ℕ))) > 0))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) > 0))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}) := by
  sorry

theorem proof_gap_exercise_2115_5
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (2 : ℕ))) > 0))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) > 0))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x /. (1 + (x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_7 x) = (((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (F_5 x)))))))}) := by
  sorry

theorem proof_gap_exercise_2115_6
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (2 : ℕ))) > 0))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) > 0))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}))
  (h5 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x /. (1 + (x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_7 x) = (((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (F_5 x)))))))}))
  : ({F_10 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_8 t) x) = ((x /. (1 + (x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_10 x) = (((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (F_8 x)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_11 x) = ((((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (Real.log (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + C))))))}) := by
  sorry

theorem proof_gap_exercise_2115_7
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (2 : ℕ))) > 0))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) > 0))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}))
  (h5 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x /. (1 + (x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_7 x) = (((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (F_5 x)))))))}))
  (h6 : ({F_10 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_8 t) x) = ((x /. (1 + (x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_10 x) = (((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (F_8 x)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_11 x) = ((((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (Real.log (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + C))))))}))
  : ({F_12 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_12 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_13 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_13 x) = ((((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (Real.log (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + C))))))}) := by
  sorry

theorem proof_gap_exercise_2115_8
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((1 + (x ^ (2 : ℕ))) > 0))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) > 0))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}))
  (h5 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t => (t /. (Real.rpow (1 + (t ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((x /. (1 + (x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_7 x) = (((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (F_5 x)))))))}))
  (h6 : ({F_10 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_8 t) x) = ((x /. (1 + (x ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x))) ∧ ((F_10 x) = (((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (F_8 x)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_11 x) = ((((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (Real.log (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + C))))))}))
  (h7 : ({F_12 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_12 t) x) = (((Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_13 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_13 x) = ((((x * (Real.log (x + (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) /. (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) - (Real.log (Real.rpow (1 + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + C))))))}))
  : (exists (C : ℝ), (C ∈ (Set.univ : Set ℝ))) := by
  sorry
