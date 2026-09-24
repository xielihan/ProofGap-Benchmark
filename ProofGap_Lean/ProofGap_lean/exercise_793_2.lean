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

-- exercise: exercise_793_2

theorem proof_gap_exercise_793_2_1
  (f : (ℝ -> ℝ))
  (x' : (ℕ -> ℝ))
  (x'' : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h2 : v_uCE_uB5_0 = 1)
  : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((1 /. n) < v_uCE_uB4))))) := by
  sorry

theorem proof_gap_exercise_793_2_2
  (f : (ℝ -> ℝ))
  (x' : (ℕ -> ℝ))
  (x'' : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((1 /. n) < v_uCE_uB4))))))
  : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| = (1 /. n))))))))) := by
  sorry

theorem proof_gap_exercise_793_2_3
  (f : (ℝ -> ℝ))
  (x' : (ℕ -> ℝ))
  (x'' : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((1 /. n) < v_uCE_uB4))))))
  (h4 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| = (1 /. n))))))))))
  : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → ((1 /. n) < v_uCE_uB4)))))))) := by
  sorry

theorem proof_gap_exercise_793_2_4
  (f : (ℝ -> ℝ))
  (x' : (ℕ -> ℝ))
  (x'' : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((1 /. n) < v_uCE_uB4))))))
  (h4 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| = (1 /. n))))))))))
  (h5 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → ((1 /. n) < v_uCE_uB4)))))))))
  : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| < v_uCE_uB4)))))))) := by
  sorry

theorem proof_gap_exercise_793_2_5
  (f : (ℝ -> ℝ))
  (x' : (ℕ -> ℝ))
  (x'' : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((1 /. n) < v_uCE_uB4))))))
  (h4 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| = (1 /. n))))))))))
  (h5 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → ((1 /. n) < v_uCE_uB4)))))))))
  (h6 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| < v_uCE_uB4)))))))))
  : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((f (x' n)) - (f (x'' n))))| = (2 + ((1 /. n) ^ (2 : ℕ))))))))))) := by
  sorry

theorem proof_gap_exercise_793_2_6
  (f : (ℝ -> ℝ))
  (x' : (ℕ -> ℝ))
  (x'' : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((1 /. n) < v_uCE_uB4))))))
  (h4 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| = (1 /. n))))))))))
  (h5 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → ((1 /. n) < v_uCE_uB4)))))))))
  (h6 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| < v_uCE_uB4)))))))))
  (h7 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((f (x' n)) - (f (x'' n))))| = (2 + ((1 /. n) ^ (2 : ℕ))))))))))))
  : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((f (x' n)) - (f (x'' n))))| > v_uCE_uB5_0)))))))) := by
  sorry

theorem proof_gap_exercise_793_2_7
  (f : (ℝ -> ℝ))
  (x' : (ℕ -> ℝ))
  (x'' : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((1 /. n) < v_uCE_uB4))))))
  (h4 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| = (1 /. n))))))))))
  (h5 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → ((1 /. n) < v_uCE_uB4)))))))))
  (h6 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| < v_uCE_uB4)))))))))
  (h7 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((f (x' n)) - (f (x'' n))))| = (2 + ((1 /. n) ^ (2 : ℕ))))))))))))
  (h8 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((f (x' n)) - (f (x'' n))))| > v_uCE_uB5_0)))))))))
  : Not (UniformContinuousOn f Set.univ) := by
  sorry

theorem proof_gap_exercise_793_2_8
  (f : (ℝ -> ℝ))
  (x' : (ℕ -> ℝ))
  (x'' : (ℕ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h2 : v_uCE_uB5_0 = 1)
  (h3 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((1 /. n) < v_uCE_uB4))))))
  (h4 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| = (1 /. n))))))))))
  (h5 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → ((1 /. n) < v_uCE_uB4)))))))))
  (h6 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((x' n) - (x'' n)))| < v_uCE_uB4)))))))))
  (h7 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((f (x' n)) - (f (x'' n))))| = (2 + ((1 /. n) ^ (2 : ℕ))))))))))))
  (h8 : (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ ((1 /. n) < v_uCE_uB4)) → (((x' n) = (n + (1 /. n))) → (((x'' n) = n) → (|(((f (x' n)) - (f (x'' n))))| > v_uCE_uB5_0)))))))))
  (h9 : Not (UniformContinuousOn f Set.univ))
  : Not (UniformContinuousOn f Set.univ) := by
  sorry
