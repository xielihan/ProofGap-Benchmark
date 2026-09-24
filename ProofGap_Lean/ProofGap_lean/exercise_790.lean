import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_790

theorem proof_gap_exercise_790_1
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  : ContinuousOn f (Set.univ : Set ℝ) := by
  sorry

theorem proof_gap_exercise_790_2
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))) := by
  sorry

theorem proof_gap_exercise_790_3
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  : Bornology.IsBounded (f '' (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_790_4
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))) := by
  sorry

theorem proof_gap_exercise_790_5
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h7 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))))
  : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (|(((x n) - (x' n)))| = ((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))) ∧ (((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))) < v_uCE_uB4))))))) := by
  sorry

theorem proof_gap_exercise_790_6
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h7 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (|(((x n) - (x' n)))| = ((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))) ∧ (((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))) < v_uCE_uB4))))))))
  : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))) := by
  sorry

theorem proof_gap_exercise_790_7
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h7 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (|(((x n) - (x' n)))| = ((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))) ∧ (((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))) < v_uCE_uB4))))))))
  (h9 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))) := by
  sorry

theorem proof_gap_exercise_790_8
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h7 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (|(((x n) - (x' n)))| = ((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))) ∧ (((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))) < v_uCE_uB4))))))))
  (h9 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h10 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  : Not (UniformContinuousOn f (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_790_9
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h7 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (|(((x n) - (x' n)))| = ((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))) ∧ (((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))) < v_uCE_uB4))))))))
  (h9 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h10 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  (h11 : Not (UniformContinuousOn f (Set.univ : Set ℝ)))
  : ContinuousOn f (Set.univ : Set ℝ) := by
  sorry

theorem proof_gap_exercise_790_10
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h7 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (|(((x n) - (x' n)))| = ((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))) ∧ (((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))) < v_uCE_uB4))))))))
  (h9 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h10 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  (h11 : Not (UniformContinuousOn f (Set.univ : Set ℝ)))
  (h12 : ContinuousOn f (Set.univ : Set ℝ))
  : Bornology.IsBounded (f '' (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_790_11
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h7 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (|(((x n) - (x' n)))| = ((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))) ∧ (((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))) < v_uCE_uB4))))))))
  (h9 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h10 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  (h11 : Not (UniformContinuousOn f (Set.univ : Set ℝ)))
  (h12 : ContinuousOn f (Set.univ : Set ℝ))
  (h13 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  : Not (UniformContinuousOn f (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_790_12
  (f : (ℝ -> ℝ))
  (x : (ℕ -> ℝ))
  (SingleDeri_x : (ℕ -> ℝ))
  (h1 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((f t) = (Real.sin (t ^ (2 : ℕ)))))))
  (h2 : ContinuousOn f (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (|((f t))| ≤ 1))))
  (h4 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x : ℕ → _) n) = (Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((x' : ℕ → _) n) = (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))
  (h7 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.univ : Set ℝ)) ∧ ((x' n) ∈ (Set.univ : Set ℝ))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (|(((x n) - (x' n)))| = ((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))))) ∧ (((Real.pi /. 2) /. ((Real.rpow ((n * Real.pi) /. 2) (((2 : ℝ))⁻¹)) + (Real.rpow (((n + 1) * Real.pi) /. 2) (((2 : ℝ))⁻¹)))) < v_uCE_uB4))))))))
  (h9 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h10 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  (h11 : Not (UniformContinuousOn f (Set.univ : Set ℝ)))
  (h12 : ContinuousOn f (Set.univ : Set ℝ))
  (h13 : Bornology.IsBounded (f '' (Set.univ : Set ℝ)))
  (h14 : Not (UniformContinuousOn f (Set.univ : Set ℝ)))
  : ((ContinuousOn f (Set.univ : Set ℝ)) ∧ (Bornology.IsBounded (f '' (Set.univ : Set ℝ)))) ∧ (Not (UniformContinuousOn f (Set.univ : Set ℝ))) := by
  sorry
