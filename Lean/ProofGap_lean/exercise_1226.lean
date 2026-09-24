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

-- exercise: exercise_1226

theorem proof_gap_exercise_1226_1
  (T : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((T (m, x)) = ((1 /. ((2 : ℕ) ^ (m - 1))) * (Real.cos (m * (Real.arccos x))))))))
  : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x) = ((m /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x))))))))) := by
  sorry

theorem proof_gap_exercise_1226_2
  (T : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((T (m, x)) = ((1 /. ((2 : ℕ) ^ (m - 1))) * (Real.cos (m * (Real.arccos x))))))))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x) = ((m /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x))))))))))
  : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x) = (((-((m ^ (2 : ℕ)) /. (((2 : ℕ) ^ (m - 1)) * (1 - (x ^ (2 : ℕ)))))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (3 /. 2)))) * (Real.sin (m * (Real.arccos x)))))))))) := by
  sorry

theorem proof_gap_exercise_1226_3
  (T : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((T (m, x)) = ((1 /. ((2 : ℕ) ^ (m - 1))) * (Real.cos (m * (Real.arccos x))))))))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x) = ((m /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x))))))))))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x) = (((-((m ^ (2 : ℕ)) /. (((2 : ℕ) ^ (m - 1)) * (1 - (x ^ (2 : ℕ)))))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (3 /. 2)))) * (Real.sin (m * (Real.arccos x)))))))))))
  : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m ^ (2 : ℕ)) /. ((2 : ℕ) ^ (m - 1)))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x)))))))))) := by
  sorry

theorem proof_gap_exercise_1226_4
  (T : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((T (m, x)) = ((1 /. ((2 : ℕ) ^ (m - 1))) * (Real.cos (m * (Real.arccos x))))))))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x) = ((m /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x))))))))))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x) = (((-((m ^ (2 : ℕ)) /. (((2 : ℕ) ^ (m - 1)) * (1 - (x ^ (2 : ℕ)))))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (3 /. 2)))) * (Real.sin (m * (Real.arccos x)))))))))))
  (h4 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m ^ (2 : ℕ)) /. ((2 : ℕ) ^ (m - 1)))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x)))))))))))
  : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m : ℝ) ^ (2 : ℕ))) * (T (m, x))) + (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x)))))))) := by
  sorry

theorem proof_gap_exercise_1226_5
  (T : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((T (m, x)) = ((1 /. ((2 : ℕ) ^ (m - 1))) * (Real.cos (m * (Real.arccos x))))))))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x) = ((m /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x))))))))))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x) = (((-((m ^ (2 : ℕ)) /. (((2 : ℕ) ^ (m - 1)) * (1 - (x ^ (2 : ℕ)))))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (3 /. 2)))) * (Real.sin (m * (Real.arccos x)))))))))))
  (h4 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m ^ (2 : ℕ)) /. ((2 : ℕ) ^ (m - 1)))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x)))))))))))
  (h5 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m : ℝ) ^ (2 : ℕ))) * (T (m, x))) + (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x)))))))))
  : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) - (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x))) + ((m ^ (2 : ℕ)) * (T (m, x)))) = 0))))) := by
  sorry

theorem proof_gap_exercise_1226_6
  (T : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((T (m, x)) = ((1 /. ((2 : ℕ) ^ (m - 1))) * (Real.cos (m * (Real.arccos x))))))))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x) = ((m /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x))))))))))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x) = (((-((m ^ (2 : ℕ)) /. (((2 : ℕ) ^ (m - 1)) * (1 - (x ^ (2 : ℕ)))))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (3 /. 2)))) * (Real.sin (m * (Real.arccos x)))))))))))
  (h4 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m ^ (2 : ℕ)) /. ((2 : ℕ) ^ (m - 1)))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x)))))))))))
  (h5 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m : ℝ) ^ (2 : ℕ))) * (T (m, x))) + (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x)))))))))
  (h6 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) - (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x))) + ((m ^ (2 : ℕ)) * (T (m, x)))) = 0))))))
  : (forall (x : ℝ) (m : ℕ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) - (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x))) + ((m ^ (2 : ℕ)) * (T (m, x)))) = 0))) := by
  sorry

theorem proof_gap_exercise_1226_7
  (T : (ℕ × ℝ -> ℝ))
  (h1 : (forall (m : ℕ) (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.Icc (-(1 : ℝ)) 1))) → ((T (m, x)) = ((1 /. ((2 : ℕ) ^ (m - 1))) * (Real.cos (m * (Real.arccos x))))))))
  (h2 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x) = ((m /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x))))))))))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → ((iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x) = (((-((m ^ (2 : ℕ)) /. (((2 : ℕ) ^ (m - 1)) * (1 - (x ^ (2 : ℕ)))))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (3 /. 2)))) * (Real.sin (m * (Real.arccos x)))))))))))
  (h4 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m ^ (2 : ℕ)) /. ((2 : ℕ) ^ (m - 1)))) * (Real.cos (m * (Real.arccos x)))) + (((m * x) /. (((2 : ℕ) ^ (m - 1)) * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (Real.sin (m * (Real.arccos x)))))))))))
  (h5 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) = (((-((m : ℝ) ^ (2 : ℕ))) * (T (m, x))) + (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x)))))))))
  (h6 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) - (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x))) + ((m ^ (2 : ℕ)) * (T (m, x)))) = 0))))))
  (h7 : (forall (x : ℝ) (m : ℕ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) - (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x))) + ((m ^ (2 : ℕ)) * (T (m, x)))) = 0))))
  : (forall (x : ℝ) (m : ℕ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℕ))) ∧ (|(x)| < 1)) → (((((1 - (x ^ (2 : ℕ))) * (iteratedDeriv 2 (fun t_1 => (T (m, t_1))) x)) - (x * (iteratedDeriv 1 (fun t_1 => (T (m, t_1))) x))) + ((m ^ (2 : ℕ)) * (T (m, x)))) = 0))) := by
  sorry
