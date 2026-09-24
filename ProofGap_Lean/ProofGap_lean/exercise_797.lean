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

-- exercise: exercise_797

theorem proof_gap_exercise_797_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((f x) = ((Real.exp x) * (Real.cos (1 /. x)))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : x = (fun (n : ℕ) => (2 /. (((2 * n) + 1) * Real.pi))))
  (h4 : x' = (fun (n : ℕ) => (1 /. (n * Real.pi))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))) := by
  sorry

theorem proof_gap_exercise_797_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((f x) = ((Real.exp x) * (Real.cos (1 /. x)))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : x = (fun (n : ℕ) => (2 /. (((2 * n) + 1) * Real.pi))))
  (h4 : x' = (fun (n : ℕ) => (1 /. (n * Real.pi))))
  (h5 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → ((|(((x n) - (x' n)))| = (1 /. ((((2 * n) + 1) * n) * Real.pi))) ∧ ((1 /. ((((2 * n) + 1) * n) * Real.pi)) < v_uCE_uB4)))))))) := by
  sorry

theorem proof_gap_exercise_797_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((f x) = ((Real.exp x) * (Real.cos (1 /. x)))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : x = (fun (n : ℕ) => (2 /. (((2 * n) + 1) * Real.pi))))
  (h4 : x' = (fun (n : ℕ) => (1 /. (n * Real.pi))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → ((|(((x n) - (x' n)))| = (1 /. ((((2 * n) + 1) * n) * Real.pi))) ∧ ((1 /. ((((2 * n) + 1) * n) * Real.pi)) < v_uCE_uB4)))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|(((f (x n)) - (f (x' n))))| = (Real.exp (1 /. (n * Real.pi)))) ∧ ((Real.exp (1 /. (n * Real.pi))) > 1)))) := by
  sorry

theorem proof_gap_exercise_797_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((f x) = ((Real.exp x) * (Real.cos (1 /. x)))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : x = (fun (n : ℕ) => (2 /. (((2 * n) + 1) * Real.pi))))
  (h4 : x' = (fun (n : ℕ) => (1 /. (n * Real.pi))))
  (h5 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((|(((x n) - (x' n)))| = (1 /. ((((2 * n) + 1) * n) * Real.pi))) ∧ ((1 /. ((((2 * n) + 1) * n) * Real.pi)) < v_uCE_uB4)))))))))
  (h7 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((|(((f (x n)) - (f (x' n))))| = (Real.exp (1 /. (n * Real.pi)))) ∧ ((Real.exp (1 /. (n * Real.pi))) > 1)))))
  : Not (UniformContinuousOn f (Set.Ioo 0 1)) := by
  sorry

theorem proof_gap_exercise_797_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((f x) = ((Real.exp x) * (Real.cos (1 /. x)))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : x = (fun (n : ℕ) => (2 /. (((2 * n) + 1) * Real.pi))))
  (h4 : x' = (fun (n : ℕ) => (1 /. (n * Real.pi))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → ((|(((x n) - (x' n)))| = (1 /. ((((2 * n) + 1) * n) * Real.pi))) ∧ ((1 /. ((((2 * n) + 1) * n) * Real.pi)) < v_uCE_uB4)))))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|(((f (x n)) - (f (x' n))))| = (Real.exp (1 /. (n * Real.pi)))) ∧ ((Real.exp (1 /. (n * Real.pi))) > 1)))))
  (h8 : Not (UniformContinuousOn f (Set.Ioo 0 1)))
  : Not (UniformContinuousOn f (Set.Ioo 0 1)) := by
  sorry
