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

-- exercise: exercise_1781

theorem proof_gap_exercise_1781_1
  (a : ℝ)
  (C : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : C ∈ (Set.univ : Set ℝ))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → ((-(Real.pi /. 2)) < t))))) := by
  sorry

theorem proof_gap_exercise_1781_2
  (a : ℝ)
  (C : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → ((-(Real.pi /. 2)) < t))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → (t < (Real.pi /. 2)))))) := by
  sorry

theorem proof_gap_exercise_1781_3
  (a : ℝ)
  (C : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → ((-(Real.pi /. 2)) < t))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → (t < (Real.pi /. 2)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2)) = ((a ^ (3 : ℕ)) * (((1 : ℝ) /. (Real.cos t)) ^ (3 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1781_4
  (a : ℝ)
  (C : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → ((-(Real.pi /. 2)) < t))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → (t < (Real.pi /. 2)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2)) = ((a ^ (3 : ℕ)) * (((1 : ℝ) /. (Real.cos t)) ^ (3 : ℕ)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((fderiv ℝ (fun (x_1 : ℝ) => x_1)) = ((a * (((1 : ℝ) /. (Real.cos t)) ^ (2 : ℕ))) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))))))) := by
  sorry

theorem proof_gap_exercise_1781_5
  (a : ℝ)
  (C : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → ((-(Real.pi /. 2)) < t))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → (t < (Real.pi /. 2)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2)) = ((a ^ (3 : ℕ)) * (((1 : ℝ) /. (Real.cos t)) ^ (3 : ℕ)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((fderiv ℝ (fun (x_1 : ℝ) => x_1)) = ((a * (((1 : ℝ) /. (Real.cos t)) ^ (2 : ℕ))) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((Real.cos t) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = ((1 /. (a ^ (2 : ℕ))) * (F_3 t)))))))}) := by
  sorry

theorem proof_gap_exercise_1781_6
  (a : ℝ)
  (C : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → ((-(Real.pi /. 2)) < t))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → (t < (Real.pi /. 2)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2)) = ((a ^ (3 : ℕ)) * (((1 : ℝ) /. (Real.cos t)) ^ (3 : ℕ)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((fderiv ℝ (fun (x_1 : ℝ) => x_1)) = ((a * (((1 : ℝ) /. (Real.cos t)) ^ (2 : ℕ))) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))))))))
  (h7 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((Real.cos t) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = ((1 /. (a ^ (2 : ℕ))) * (F_3 t)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = ((Real.cos t) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = ((1 /. (a ^ (2 : ℕ))) * (F_5 t)))))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → ((F_7 t) = (((1 /. (a ^ (2 : ℕ))) * (Real.sin t)) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1781_7
  (a : ℝ)
  (C : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → ((-(Real.pi /. 2)) < t))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → (t < (Real.pi /. 2)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2)) = ((a ^ (3 : ℕ)) * (((1 : ℝ) /. (Real.cos t)) ^ (3 : ℕ)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((fderiv ℝ (fun (x_1 : ℝ) => x_1)) = ((a * (((1 : ℝ) /. (Real.cos t)) ^ (2 : ℕ))) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))))))))
  (h7 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((Real.cos t) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = ((1 /. (a ^ (2 : ℕ))) * (F_3 t)))))))}))
  (h8 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = ((Real.cos t) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = ((1 /. (a ^ (2 : ℕ))) * (F_5 t)))))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → ((F_7 t) = (((1 /. (a ^ (2 : ℕ))) * (Real.sin t)) + C_1))))))}))
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → ((((1 /. (a ^ (2 : ℕ))) * (Real.sin t)) + C) = (((1 /. (a ^ (2 : ℕ))) * ((Real.tan t) /. (Real.rpow (1 + ((Real.tan t) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + C)))) := by
  sorry

theorem proof_gap_exercise_1781_8
  (a : ℝ)
  (C : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → ((-(Real.pi /. 2)) < t))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (x = (a * (Real.tan t)))) → (t < (Real.pi /. 2)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2)) = ((a ^ (3 : ℕ)) * (((1 : ℝ) /. (Real.cos t)) ^ (3 : ℕ)))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (t : ℝ), (((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) ∧ (x = (a * (Real.tan t)))) → ((fderiv ℝ (fun (x_1 : ℝ) => x_1)) = ((a * (((1 : ℝ) /. (Real.cos t)) ^ (2 : ℕ))) • (fderiv ℝ (fun (t_1 : ℝ) => t_1)))))))))
  (h7 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((Real.cos t) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = ((1 /. (a ^ (2 : ℕ))) * (F_3 t)))))))}))
  (h8 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = ((Real.cos t) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = ((1 /. (a ^ (2 : ℕ))) * (F_5 t)))))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → ((F_7 t) = (((1 /. (a ^ (2 : ℕ))) * (Real.sin t)) + C_1))))))}))
  (h9 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ ((-(Real.pi /. 2)) < t)) ∧ (t < (Real.pi /. 2))) → ((((1 /. (a ^ (2 : ℕ))) * (Real.sin t)) + C) = (((1 /. (a ^ (2 : ℕ))) * ((Real.tan t) /. (Real.rpow (1 + ((Real.tan t) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + C)))))
  : ({F_8 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_8 t_1) x) = ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + (a ^ (2 : ℕ))) (3 /. 2))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_9 x) = ((x /. ((a ^ (2 : ℕ)) * (Real.rpow ((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + C_1))))))}) := by
  sorry
