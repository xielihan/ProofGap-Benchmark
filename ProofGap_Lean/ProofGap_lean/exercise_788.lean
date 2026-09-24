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

-- exercise: exercise_788

theorem proof_gap_exercise_788_1
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  : ContinuousOn f (Set.Ioo 0 1) := by
  sorry

theorem proof_gap_exercise_788_2
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  (h2 : ContinuousOn f (Set.Ioo 0 1))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x : ℤ → _) n) = (1 /. n))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x' : ℤ → _) n) = (1 /. (n + 1)))))
  : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))) := by
  sorry

theorem proof_gap_exercise_788_3
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  (h2 : ContinuousOn f (Set.Ioo 0 1))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x : ℤ → _) n) = (1 /. n))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x' : ℤ → _) n) = (1 /. (n + 1)))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), ((((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((x n) - (x' n)))| = (1 /. (n * (n + 1))))) ∧ ((1 /. (n * (n + 1))) < v_uCE_uB4))))))) := by
  sorry

theorem proof_gap_exercise_788_4
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  (h2 : ContinuousOn f (Set.Ioo 0 1))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x : ℤ → _) n) = (1 /. n))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x' : ℤ → _) n) = (1 /. (n + 1)))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), ((((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((x n) - (x' n)))| = (1 /. (n * (n + 1))))) ∧ ((1 /. (n * (n + 1))) < v_uCE_uB4))))))))
  : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))) := by
  sorry

theorem proof_gap_exercise_788_5
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  (h2 : ContinuousOn f (Set.Ioo 0 1))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x : ℤ → _) n) = (1 /. n))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x' : ℤ → _) n) = (1 /. (n + 1)))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), ((((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((x n) - (x' n)))| = (1 /. (n * (n + 1))))) ∧ ((1 /. (n * (n + 1))) < v_uCE_uB4))))))))
  (h7 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))) := by
  sorry

theorem proof_gap_exercise_788_6
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  (h2 : ContinuousOn f (Set.Ioo 0 1))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x : ℤ → _) n) = (1 /. n))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x' : ℤ → _) n) = (1 /. (n + 1)))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), ((((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((x n) - (x' n)))| = (1 /. (n * (n + 1))))) ∧ ((1 /. (n * (n + 1))) < v_uCE_uB4))))))))
  (h7 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  : Not (UniformContinuousOn f (Set.Ioo 0 1)) := by
  sorry

theorem proof_gap_exercise_788_7
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  (h2 : ContinuousOn f (Set.Ioo 0 1))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x : ℤ → _) n) = (1 /. n))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x' : ℤ → _) n) = (1 /. (n + 1)))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), ((((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((x n) - (x' n)))| = (1 /. (n * (n + 1))))) ∧ ((1 /. (n * (n + 1))) < v_uCE_uB4))))))))
  (h7 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  (h9 : Not (UniformContinuousOn f (Set.Ioo 0 1)))
  : ContinuousOn f (Set.Ioo 0 1) := by
  sorry

theorem proof_gap_exercise_788_8
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  (h2 : ContinuousOn f (Set.Ioo 0 1))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x : ℤ → _) n) = (1 /. n))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x' : ℤ → _) n) = (1 /. (n + 1)))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), ((((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((x n) - (x' n)))| = (1 /. (n * (n + 1))))) ∧ ((1 /. (n * (n + 1))) < v_uCE_uB4))))))))
  (h7 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  (h9 : Not (UniformContinuousOn f (Set.Ioo 0 1)))
  (h10 : ContinuousOn f (Set.Ioo 0 1))
  : Not (UniformContinuousOn f (Set.Ioo 0 1)) := by
  sorry

theorem proof_gap_exercise_788_9
  (f : (ℝ -> ℝ))
  (x : (ℤ -> ℝ))
  (SingleDeri_x : (ℤ -> ℝ))
  (h1 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.Ioo 0 1))) → ((f t) = (1 /. t)))))
  (h2 : ContinuousOn f (Set.Ioo 0 1))
  (h3 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x : ℤ → _) n) = (1 /. n))))
  (h4 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2))) → (((x' : ℤ → _) n) = (1 /. (n + 1)))))
  (h5 : (forall (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) → (((x n) ∈ (Set.Ioo 0 1)) ∧ ((x' n) ∈ (Set.Ioo 0 1))))))
  (h6 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), ((((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((x n) - (x' n)))| = (1 /. (n * (n + 1))))) ∧ ((1 /. (n * (n + 1))) < v_uCE_uB4))))))))
  (h7 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (n : ℤ), (((n ∈ (Set.univ : Set ℤ)) ∧ (n ≥ 2)) ∧ (|(((f (x n)) - (f (x' n))))| = 1))))))))
  (h8 : (forall (v_uCE_uB5_0 : ℝ), ((((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB5_0)) ∧ (v_uCE_uB5_0 < 1)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (1 > v_uCE_uB5_0))))))
  (h9 : Not (UniformContinuousOn f (Set.Ioo 0 1)))
  (h10 : ContinuousOn f (Set.Ioo 0 1))
  (h11 : Not (UniformContinuousOn f (Set.Ioo 0 1)))
  : (ContinuousOn f (Set.Ioo 0 1)) ∧ (Not (UniformContinuousOn f (Set.Ioo 0 1))) := by
  sorry
