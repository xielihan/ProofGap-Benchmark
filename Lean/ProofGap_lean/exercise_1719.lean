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

-- exercise: exercise_1719

theorem proof_gap_exercise_1719_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) • (fderiv ℝ (fun (x_1 : ℝ) => x_1)))))) := by
  sorry

theorem proof_gap_exercise_1719_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) • (fderiv ℝ (fun (x_1 : ℝ) => x_1)))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}) := by
  sorry

theorem proof_gap_exercise_1719_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) • (fderiv ℝ (fun (x_1 : ℝ) => x_1)))))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  : ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_4 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_4 t) x) = ((iteratedDeriv 1 (fun t => (Real.rpow (3 /. 2) t)) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1))) ∧ ((F_5 x) = ((1 /. ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ)))) * (F_4 x)))))))}) := by
  sorry

theorem proof_gap_exercise_1719_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) • (fderiv ℝ (fun (x_1 : ℝ) => x_1)))))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h6 : ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_4 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_4 t) x) = ((iteratedDeriv 1 (fun t => (Real.rpow (3 /. 2) t)) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1))) ∧ ((F_5 x) = ((1 /. ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ)))) * (F_4 x)))))))}))
  : ({F_5 : (ℝ -> ℝ) | (exists (F_4 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_4 t) x) = ((iteratedDeriv 1 (fun t => (Real.rpow (3 /. 2) t)) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1))) ∧ ((F_5 x) = ((1 /. ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ)))) * (F_4 x)))))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_6 x) = (((1 /. (2 * ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ))))) * (Real.log |((((Real.rpow (3 : ℝ) x) - (Real.rpow (2 : ℝ) x)) /. ((Real.rpow (3 : ℝ) x) + (Real.rpow (2 : ℝ) x))))|)) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1719_5
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) • (fderiv ℝ (fun (x_1 : ℝ) => x_1)))))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h6 : ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_4 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_4 t) x) = ((iteratedDeriv 1 (fun t => (Real.rpow (3 /. 2) t)) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1))) ∧ ((F_5 x) = ((1 /. ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ)))) * (F_4 x)))))))}))
  (h7 : ({F_5 : (ℝ -> ℝ) | (exists (F_4 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_4 t) x) = ((iteratedDeriv 1 (fun t => (Real.rpow (3 /. 2) t)) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1))) ∧ ((F_5 x) = ((1 /. ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ)))) * (F_4 x)))))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_6 x) = (((1 /. (2 * ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ))))) * (Real.log |((((Real.rpow (3 : ℝ) x) - (Real.rpow (2 : ℝ) x)) /. ((Real.rpow (3 : ℝ) x) + (Real.rpow (2 : ℝ) x))))|)) + C_1))))))}))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_6 x) = (((1 /. (2 * ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ))))) * (Real.log |((((Real.rpow (3 : ℝ) x) - (Real.rpow (2 : ℝ) x)) /. ((Real.rpow (3 : ℝ) x) + (Real.rpow (2 : ℝ) x))))|)) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1719_6
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (x ≠ 0))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) • (fderiv ℝ (fun (x_1 : ℝ) => x_1))) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) • (fderiv ℝ (fun (x_1 : ℝ) => x_1)))))))
  (h5 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h6 : ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = (((Real.rpow (3 /. 2) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (exists (F_4 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_4 t) x) = ((iteratedDeriv 1 (fun t => (Real.rpow (3 /. 2) t)) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1))) ∧ ((F_5 x) = ((1 /. ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ)))) * (F_4 x)))))))}))
  (h7 : ({F_5 : (ℝ -> ℝ) | (exists (F_4 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_4 t) x) = ((iteratedDeriv 1 (fun t => (Real.rpow (3 /. 2) t)) x) /. (((Real.rpow (3 /. 2) x) ^ (2 : ℕ)) - 1))) ∧ ((F_5 x) = ((1 /. ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ)))) * (F_4 x)))))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_6 x) = (((1 /. (2 * ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ))))) * (Real.log |((((Real.rpow (3 : ℝ) x) - (Real.rpow (2 : ℝ) x)) /. ((Real.rpow (3 : ℝ) x) + (Real.rpow (2 : ℝ) x))))|)) + C_1))))))}))
  (h8 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_6 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_6 x) = (((1 /. (2 * ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ))))) * (Real.log |((((Real.rpow (3 : ℝ) x) - (Real.rpow (2 : ℝ) x)) /. ((Real.rpow (3 : ℝ) x) + (Real.rpow (2 : ℝ) x))))|)) + C_1))))))}))
  : ({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = ((((Real.rpow (2 : ℝ) x) * (Real.rpow (3 : ℝ) x)) /. ((Real.rpow (9 : ℝ) x) - (Real.rpow (4 : ℝ) x))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_8 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_8 x) = (((1 /. (2 * ((Real.log (3 : ℝ)) - (Real.log (2 : ℝ))))) * (Real.log |((((Real.rpow (3 : ℝ) x) - (Real.rpow (2 : ℝ) x)) /. ((Real.rpow (3 : ℝ) x) + (Real.rpow (2 : ℝ) x))))|)) + C_1))))))}) := by
  sorry
