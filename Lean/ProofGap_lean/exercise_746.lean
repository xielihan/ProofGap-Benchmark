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

-- exercise: exercise_746

theorem proof_gap_exercise_746_1
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (D : (Set ℝ))
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : ContinuousOn f D)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) → ((F x) = |((f x))|))))
  : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt f x_0))) := by
  sorry

theorem proof_gap_exercise_746_2
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (D : (Set ℝ))
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : ContinuousOn f D)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) → ((F x) = |((f x))|))))
  (h4 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt f x_0))))
  : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))))) := by
  sorry

theorem proof_gap_exercise_746_3
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (D : (Set ℝ))
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : ContinuousOn f D)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) → ((F x) = |((f x))|))))
  (h4 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt f x_0))))
  (h5 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (|((|((f x))| - |((f x_0))|))| ≤ |(((f x) - (f x_0)))|))))))) := by
  sorry

theorem proof_gap_exercise_746_4
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (D : (Set ℝ))
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : ContinuousOn f D)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) → ((F x) = |((f x))|))))
  (h4 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt f x_0))))
  (h5 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (|((|((f x))| - |((f x_0))|))| ≤ |(((f x) - (f x_0)))|))))))))
  : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((F x) - (F x_0)))| < v_uCE_uB5))))))))) := by
  sorry

theorem proof_gap_exercise_746_5
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (D : (Set ℝ))
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : ContinuousOn f D)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) → ((F x) = |((f x))|))))
  (h4 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt f x_0))))
  (h5 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (|((|((f x))| - |((f x_0))|))| ≤ |(((f x) - (f x_0)))|))))))))
  (h7 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((F x) - (F x_0)))| < v_uCE_uB5))))))))))
  : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt F x_0))) := by
  sorry

theorem proof_gap_exercise_746_6
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (D : (Set ℝ))
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : ContinuousOn f D)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) → ((F x) = |((f x))|))))
  (h4 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt f x_0))))
  (h5 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (|((|((f x))| - |((f x_0))|))| ≤ |(((f x) - (f x_0)))|))))))))
  (h7 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((F x) - (F x_0)))| < v_uCE_uB5))))))))))
  (h8 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt F x_0))))
  : ContinuousOn F D := by
  sorry

theorem proof_gap_exercise_746_7
  (f : (ℝ -> ℝ))
  (F : (ℝ -> ℝ))
  (D : (Set ℝ))
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : ContinuousOn f D)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) → ((F x) = |((f x))|))))
  (h4 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt f x_0))))
  (h5 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (|((|((f x))| - |((f x_0))|))| ≤ |(((f x) - (f x_0)))|))))))))
  (h7 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((F x) - (F x_0)))| < v_uCE_uB5))))))))))
  (h8 : (forall (x_0 : ℝ), (((x_0 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ D)) → (ContinuousAt F x_0))))
  (h9 : ContinuousOn F D)
  : ContinuousOn F D := by
  sorry
