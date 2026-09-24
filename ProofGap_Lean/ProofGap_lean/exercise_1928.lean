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

-- exercise: exercise_1928

theorem proof_gap_exercise_1928_1
  (x : ℝ)
  (C : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.rpow (2 + x) (((3 : ℝ))⁻¹)))
  : x = ((t ^ (3 : ℕ)) - 2) := by
  sorry

theorem proof_gap_exercise_1928_2
  (x : ℝ)
  (C : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.rpow (2 + x) (((3 : ℝ))⁻¹)))
  (h4 : x = ((t ^ (3 : ℕ)) - 2))
  : (fderiv ℝ (fun (t : ℝ) => x)) = ((3 * (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))) := by
  sorry

theorem proof_gap_exercise_1928_3
  (x : ℝ)
  (C : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.rpow (2 + x) (((3 : ℝ))⁻¹)))
  (h4 : x = ((t ^ (3 : ℕ)) - 2))
  (h5 : (fderiv ℝ (fun (t : ℝ) => x)) = ((3 * (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x_1) = (((x_1 * (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹))) /. (x_1 + (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t_1 => t_1) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = (3 * (F_3 t)))))))}) := by
  sorry

theorem proof_gap_exercise_1928_4
  (x : ℝ)
  (C : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.rpow (2 + x) (((3 : ℝ))⁻¹)))
  (h4 : x = ((t ^ (3 : ℕ)) - 2))
  (h5 : (fderiv ℝ (fun (t : ℝ) => x)) = ((3 * (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x_1) = (((x_1 * (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹))) /. (x_1 + (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t_1 => t_1) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = (3 * (F_3 t)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = (3 * (F_5 t)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_7 t_1) t) = ((((t ^ (3 : ℕ)) - t) + (((t ^ (2 : ℕ)) - (2 * t)) /. (((t ^ (3 : ℕ)) + t) - 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_8 t) = (3 * (F_7 t)))))))}) := by
  sorry

theorem proof_gap_exercise_1928_5
  (x : ℝ)
  (C : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.rpow (2 + x) (((3 : ℝ))⁻¹)))
  (h4 : x = ((t ^ (3 : ℕ)) - 2))
  (h5 : (fderiv ℝ (fun (t : ℝ) => x)) = ((3 * (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x_1) = (((x_1 * (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹))) /. (x_1 + (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t_1 => t_1) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = (3 * (F_3 t)))))))}))
  (h7 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = (3 * (F_5 t)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_7 t_1) t) = ((((t ^ (3 : ℕ)) - t) + (((t ^ (2 : ℕ)) - (2 * t)) /. (((t ^ (3 : ℕ)) + t) - 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_8 t) = (3 * (F_7 t)))))))}))
  : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_9 t_1) t) = ((((t ^ (3 : ℕ)) - t) + (((t ^ (2 : ℕ)) - (2 * t)) /. (((t ^ (3 : ℕ)) + t) - 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_10 t) = (3 * (F_9 t)))))))}) = ({F_14 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_11 t_1) t) = (((-(1 /. (4 * (t - 1)))) + ((((5 /. 4) * t) - (1 /. 2)) /. (((t ^ (2 : ℕ)) + t) + 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_14 t) = ((((3 /. 4) * (t ^ (4 : ℕ))) - ((3 /. 2) * (t ^ (2 : ℕ)))) + (3 * (F_11 t))))))))}) := by
  sorry

theorem proof_gap_exercise_1928_6
  (x : ℝ)
  (C : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.rpow (2 + x) (((3 : ℝ))⁻¹)))
  (h4 : x = ((t ^ (3 : ℕ)) - 2))
  (h5 : (fderiv ℝ (fun (t : ℝ) => x)) = ((3 * (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x_1) = (((x_1 * (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹))) /. (x_1 + (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t_1 => t_1) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = (3 * (F_3 t)))))))}))
  (h7 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = (3 * (F_5 t)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_7 t_1) t) = ((((t ^ (3 : ℕ)) - t) + (((t ^ (2 : ℕ)) - (2 * t)) /. (((t ^ (3 : ℕ)) + t) - 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_8 t) = (3 * (F_7 t)))))))}))
  (h8 : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_9 t_1) t) = ((((t ^ (3 : ℕ)) - t) + (((t ^ (2 : ℕ)) - (2 * t)) /. (((t ^ (3 : ℕ)) + t) - 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_10 t) = (3 * (F_9 t)))))))}) = ({F_14 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_11 t_1) t) = (((-(1 /. (4 * (t - 1)))) + ((((5 /. 4) * t) - (1 /. 2)) /. (((t ^ (2 : ℕ)) + t) + 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_14 t) = ((((3 /. 4) * (t ^ (4 : ℕ))) - ((3 /. 2) * (t ^ (2 : ℕ)))) + (3 * (F_11 t))))))))}))
  : ({F_18 : (ℝ -> ℝ) | (exists (F_15 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_15 t_1) t) = (((-(1 /. (4 * (t - 1)))) + ((((5 /. 4) * t) - (1 /. 2)) /. (((t ^ (2 : ℕ)) + t) + 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_18 t) = ((((3 /. 4) * (t ^ (4 : ℕ))) - ((3 /. 2) * (t ^ (2 : ℕ)))) + (3 * (F_15 t))))))))}) = ({F_19 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → ((F_19 t) = (((((((3 /. 4) * (t ^ (4 : ℕ))) - ((3 /. 2) * (t ^ (2 : ℕ)))) - ((3 /. 4) * (Real.log |((t - 1))|))) + ((15 /. 8) * (Real.log (((t ^ (2 : ℕ)) + t) + 2)))) - ((27 /. (4 * (Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.arctan (((2 * t) + 1) /. (Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)))))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1928_7
  (x : ℝ)
  (C : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.rpow (2 + x) (((3 : ℝ))⁻¹)))
  (h4 : x = ((t ^ (3 : ℕ)) - 2))
  (h5 : (fderiv ℝ (fun (t : ℝ) => x)) = ((3 * (t ^ (2 : ℕ))) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x_1) = (((x_1 * (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹))) /. (x_1 + (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t_1 => t_1) x_1)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = (3 * (F_3 t)))))))}))
  (h7 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = ((((t ^ (6 : ℕ)) - (2 * (t ^ (3 : ℕ)))) /. (((t ^ (3 : ℕ)) + t) - 2)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = (3 * (F_5 t)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_7 t_1) t) = ((((t ^ (3 : ℕ)) - t) + (((t ^ (2 : ℕ)) - (2 * t)) /. (((t ^ (3 : ℕ)) + t) - 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_8 t) = (3 * (F_7 t)))))))}))
  (h8 : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_9 t_1) t) = ((((t ^ (3 : ℕ)) - t) + (((t ^ (2 : ℕ)) - (2 * t)) /. (((t ^ (3 : ℕ)) + t) - 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_10 t) = (3 * (F_9 t)))))))}) = ({F_14 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_11 t_1) t) = (((-(1 /. (4 * (t - 1)))) + ((((5 /. 4) * t) - (1 /. 2)) /. (((t ^ (2 : ℕ)) + t) + 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_14 t) = ((((3 /. 4) * (t ^ (4 : ℕ))) - ((3 /. 2) * (t ^ (2 : ℕ)))) + (3 * (F_11 t))))))))}))
  (h9 : ({F_18 : (ℝ -> ℝ) | (exists (F_15 : (ℝ -> ℝ)), (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → (((iteratedDeriv 1 (fun t_1 => F_15 t_1) t) = (((-(1 /. (4 * (t - 1)))) + ((((5 /. 4) * t) - (1 /. 2)) /. (((t ^ (2 : ℕ)) + t) + 2))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_18 t) = ((((3 /. 4) * (t ^ (4 : ℕ))) - ((3 /. 2) * (t ^ (2 : ℕ)))) + (3 * (F_15 t))))))))}) = ({F_19 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ 1)) → ((F_19 t) = (((((((3 /. 4) * (t ^ (4 : ℕ))) - ((3 /. 2) * (t ^ (2 : ℕ)))) - ((3 /. 4) * (Real.log |((t - 1))|))) + ((15 /. 8) * (Real.log (((t ^ (2 : ℕ)) + t) + 2)))) - ((27 /. (4 * (Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.arctan (((2 * t) + 1) /. (Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)))))) + C_1))))))}))
  : ({F_20 : (ℝ -> ℝ) | (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((iteratedDeriv 1 (fun t_1 => F_20 t_1) x_1) = (((x_1 * (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹))) /. (x_1 + (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)))) * (iteratedDeriv 1 (fun t_1 => t_1) x_1)))))}) = ({F_21 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (-(1 : ℝ)))) → ((F_21 x_1) = (((((((3 /. 4) * ((Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)) ^ (4 : ℕ))) - ((3 /. 2) * ((Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)) ^ (2 : ℕ)))) - ((3 /. 4) * (Real.log |(((Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)) - 1))|))) + ((15 /. 8) * (Real.log ((((Real.rpow (2 + x_1) (((3 : ℝ))⁻¹)) ^ (2 : ℕ)) + (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹))) + 2)))) - ((27 /. (4 * (Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.arctan (((2 * (Real.rpow (2 + x_1) (((3 : ℝ))⁻¹))) + 1) /. (Real.rpow (7 : ℝ) (((2 : ℝ))⁻¹)))))) + C_1))))))}) := by
  sorry
