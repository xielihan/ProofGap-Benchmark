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

-- exercise: exercise_793_1

theorem proof_gap_exercise_793_1_1
  (f : (ℝ -> ℝ))
  (l : ℝ)
  (h1 : (l ∈ (Set.univ : Set ℝ)) ∧ (l ∈ ({x_3 : ℝ | 0 < x_3})))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| = |(((x_1 ^ (2 : ℕ)) - (x_2 ^ (2 : ℕ))))|))))) := by
  sorry

theorem proof_gap_exercise_793_1_2
  (f : (ℝ -> ℝ))
  (l : ℝ)
  (h1 : (l ∈ (Set.univ : Set ℝ)) ∧ (l ∈ ({x_3 : ℝ | 0 < x_3})))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| = |(((x_1 ^ (2 : ℕ)) - (x_2 ^ (2 : ℕ))))|))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| ≤ ((2 * l) * |((x_1 - x_2))|)))))) := by
  sorry

theorem proof_gap_exercise_793_1_3
  (f : (ℝ -> ℝ))
  (l : ℝ)
  (h1 : (l ∈ (Set.univ : Set ℝ)) ∧ (l ∈ ({x_3 : ℝ | 0 < x_3})))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| = |(((x_1 ^ (2 : ℕ)) - (x_2 ^ (2 : ℕ))))|))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| ≤ ((2 * l) * |((x_1 - x_2))|)))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (v_uCE_uB5 /. (2 * l))) → (v_uCE_uB4 > 0)))))) := by
  sorry

theorem proof_gap_exercise_793_1_4
  (f : (ℝ -> ℝ))
  (l : ℝ)
  (h1 : (l ∈ (Set.univ : Set ℝ)) ∧ (l ∈ ({x_3 : ℝ | 0 < x_3})))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| = |(((x_1 ^ (2 : ℕ)) - (x_2 ^ (2 : ℕ))))|))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| ≤ ((2 * l) * |((x_1 - x_2))|)))))))
  (h5 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (v_uCE_uB5 /. (2 * l))) → (v_uCE_uB4 > 0)))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (v_uCE_uB5 /. (2 * l))) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))) := by
  sorry

theorem proof_gap_exercise_793_1_5
  (f : (ℝ -> ℝ))
  (l : ℝ)
  (h1 : (l ∈ (Set.univ : Set ℝ)) ∧ (l ∈ ({x_3 : ℝ | 0 < x_3})))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| = |(((x_1 ^ (2 : ℕ)) - (x_2 ^ (2 : ℕ))))|))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| ≤ ((2 * l) * |((x_1 - x_2))|)))))))
  (h5 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (v_uCE_uB5 /. (2 * l))) → (v_uCE_uB4 > 0)))))))
  (h6 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (v_uCE_uB5 /. (2 * l))) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))))
  : UniformContinuousOn f (Set.Ioo (-l) l) := by
  sorry

theorem proof_gap_exercise_793_1_6
  (f : (ℝ -> ℝ))
  (l : ℝ)
  (h1 : (l ∈ (Set.univ : Set ℝ)) ∧ (l ∈ ({x_3 : ℝ | 0 < x_3})))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (x ^ (2 : ℕ))))))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| = |(((x_1 ^ (2 : ℕ)) - (x_2 ^ (2 : ℕ))))|))))))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), ((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| ≤ ((2 * l) * |((x_1 - x_2))|)))))))
  (h5 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (v_uCE_uB5 /. (2 * l))) → (v_uCE_uB4 > 0)))))))
  (h6 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (v_uCE_uB5 /. (2 * l))) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (x_1 ∈ (Set.Ioo (-l) l))) ∧ (x_2 ∈ (Set.Ioo (-l) l))) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))))
  (h7 : UniformContinuousOn f (Set.Ioo (-l) l))
  : UniformContinuousOn f (Set.Ioo (-l) l) := by
  sorry
