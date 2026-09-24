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

-- exercise: exercise_1770

theorem proof_gap_exercise_1770_1
  (h1 : t = (2 - (5 * (x ^ (3 : ℕ)))))
  : (x ^ (3 : ℕ)) = ((1 /. 5) * (2 - t)) := by
  sorry

theorem proof_gap_exercise_1770_2
  (h1 : t = (2 - (5 * (x ^ (3 : ℕ)))))
  (h2 : (x ^ (3 : ℕ)) = ((1 /. 5) * (2 - t)))
  : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_1770_3
  (h1 : t = (2 - (5 * (x ^ (3 : ℕ)))))
  (h2 : (x ^ (3 : ℕ)) = ((1 /. 5) * (2 - t)))
  (h3 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))))
  : (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))) := by
  sorry

theorem proof_gap_exercise_1770_4
  (h1 : t = (2 - (5 * (x ^ (3 : ℕ)))))
  (h2 : (x ^ (3 : ℕ)) = ((1 /. 5) * (2 - t)))
  (h3 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))))
  (h4 : (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))) := by
  sorry

theorem proof_gap_exercise_1770_5
  (h1 : t = (2 - (5 * (x ^ (3 : ℕ)))))
  (h2 : (x ^ (3 : ℕ)) = ((1 /. 5) * (2 - t)))
  (h3 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))))
  (h4 : (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h5 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = (((x ^ (5 : ℕ)) * (Real.rpow (2 - (5 * (x ^ (3 : ℕ)))) (2 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = (((Real.rpow t (2 /. 3)) * (2 - t)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = ((-(1 /. 75)) * (F_3 t)))))))}) := by
  sorry

theorem proof_gap_exercise_1770_6
  (h1 : t = (2 - (5 * (x ^ (3 : ℕ)))))
  (h2 : (x ^ (3 : ℕ)) = ((1 /. 5) * (2 - t)))
  (h3 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))))
  (h4 : (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h5 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = (((x ^ (5 : ℕ)) * (Real.rpow (2 - (5 * (x ^ (3 : ℕ)))) (2 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = (((Real.rpow t (2 /. 3)) * (2 - t)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = ((-(1 /. 75)) * (F_3 t)))))))}))
  : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = (((Real.rpow t (2 /. 3)) * (2 - t)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = ((-(1 /. 75)) * (F_5 t)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_7 t_1) t) = (((2 * (Real.rpow t (2 /. 3))) - (Real.rpow t (5 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_8 t) = ((-(1 /. 75)) * (F_7 t)))))))}) := by
  sorry

theorem proof_gap_exercise_1770_7
  (h1 : t = (2 - (5 * (x ^ (3 : ℕ)))))
  (h2 : (x ^ (3 : ℕ)) = ((1 /. 5) * (2 - t)))
  (h3 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))))
  (h4 : (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h5 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = (((x ^ (5 : ℕ)) * (Real.rpow (2 - (5 * (x ^ (3 : ℕ)))) (2 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = (((Real.rpow t (2 /. 3)) * (2 - t)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = ((-(1 /. 75)) * (F_3 t)))))))}))
  (h7 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = (((Real.rpow t (2 /. 3)) * (2 - t)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = ((-(1 /. 75)) * (F_5 t)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_7 t_1) t) = (((2 * (Real.rpow t (2 /. 3))) - (Real.rpow t (5 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_8 t) = ((-(1 /. 75)) * (F_7 t)))))))}))
  : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_9 t_1) t) = (((2 * (Real.rpow t (2 /. 3))) - (Real.rpow t (5 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_10 t) = ((-(1 /. 75)) * (F_9 t)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((F_11 t) = ((((-(2 /. 125)) * (Real.rpow t (5 /. 3))) + ((1 /. 200) * (Real.rpow t (8 /. 3)))) + C))))))}) := by
  sorry

theorem proof_gap_exercise_1770_8
  (h1 : t = (2 - (5 * (x ^ (3 : ℕ)))))
  (h2 : (x ^ (3 : ℕ)) = ((1 /. 5) * (2 - t)))
  (h3 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))))
  (h4 : (((1 /. 3) * (x ^ (3 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => (x ^ (3 : ℕ))))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h5 : ((x ^ (5 : ℕ)) • (fderiv ℝ (fun (x : ℝ) => x))) = (((-(1 /. 75)) * (2 - t)) • (fderiv ℝ (fun (t : ℝ) => t))))
  (h6 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x) = (((x ^ (5 : ℕ)) * (Real.rpow (2 - (5 * (x ^ (3 : ℕ)))) (2 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_4 : (ℝ -> ℝ) | (exists (F_3 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_3 t_1) t) = (((Real.rpow t (2 /. 3)) * (2 - t)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_4 t) = ((-(1 /. 75)) * (F_3 t)))))))}))
  (h7 : ({F_6 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_5 t_1) t) = (((Real.rpow t (2 /. 3)) * (2 - t)) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_6 t) = ((-(1 /. 75)) * (F_5 t)))))))}) = ({F_8 : (ℝ -> ℝ) | (exists (F_7 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_7 t_1) t) = (((2 * (Real.rpow t (2 /. 3))) - (Real.rpow t (5 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_8 t) = ((-(1 /. 75)) * (F_7 t)))))))}))
  (h8 : ({F_10 : (ℝ -> ℝ) | (exists (F_9 : (ℝ -> ℝ)), (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t_1 => F_9 t_1) t) = (((2 * (Real.rpow t (2 /. 3))) - (Real.rpow t (5 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) t))) ∧ ((F_10 t) = ((-(1 /. 75)) * (F_9 t)))))))}) = ({F_11 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((F_11 t) = ((((-(2 /. 125)) * (Real.rpow t (5 /. 3))) + ((1 /. 200) * (Real.rpow t (8 /. 3)))) + C))))))}))
  : ({F_12 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_12 t_1) x) = (((x ^ (5 : ℕ)) * (Real.rpow (2 - (5 * (x ^ (3 : ℕ)))) (2 /. 3))) * (iteratedDeriv 1 (fun t_1 => t_1) x)))))}) = ({F_13 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_13 x) = (((-((6 + (25 * (x ^ (3 : ℕ)))) /. 1000)) * (Real.rpow (2 - (5 * (x ^ (3 : ℕ)))) (5 /. 3))) + C))))))}) := by
  sorry
