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

-- exercise: exercise_787

theorem proof_gap_exercise_787_1
  (f : (ℝ -> ℝ))
  (E : (Set ℝ))
  (h1 : E ⊆ (Set.univ : Set ℝ))
  : (ContinuousOn f E) ↔ (forall (v_uCE_uB5 : ℝ) (x_0 : ℝ), (((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB5 > 0)) ∧ (x_0 ∈ E)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ E)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))) := by
  sorry

theorem proof_gap_exercise_787_2
  (f : (ℝ -> ℝ))
  (E : (Set ℝ))
  (h1 : E ⊆ (Set.univ : Set ℝ))
  (h2 : (ContinuousOn f E) ↔ (forall (v_uCE_uB5 : ℝ) (x_0 : ℝ), (((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB5 > 0)) ∧ (x_0 ∈ E)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ E)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))))
  : (Not (UniformContinuousOn f E)) ↔ (exists (v_uCE_uB5_0 : ℝ), (((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5_0 > 0)) ∧ (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ E)) ∧ (x_2 ∈ E)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (|(((f x_1) - (f x_2)))| ≥ v_uCE_uB5_0))))))) := by
  sorry

theorem proof_gap_exercise_787_3
  (f : (ℝ -> ℝ))
  (E : (Set ℝ))
  (h1 : E ⊆ (Set.univ : Set ℝ))
  (h2 : (ContinuousOn f E) ↔ (forall (v_uCE_uB5 : ℝ) (x_0 : ℝ), (((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB5 > 0)) ∧ (x_0 ∈ E)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ E)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))))
  (h3 : (Not (UniformContinuousOn f E)) ↔ (exists (v_uCE_uB5_0 : ℝ), (((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5_0 > 0)) ∧ (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ E)) ∧ (x_2 ∈ E)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (|(((f x_1) - (f x_2)))| ≥ v_uCE_uB5_0))))))))
  : ((forall (v_uCE_uB5 : ℝ) (x_0 : ℝ), (((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB5 > 0)) ∧ (x_0 ∈ E)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ E)) ∧ (|((x - x_0))| < v_uCE_uB4)) → (|(((f x) - (f x_0)))| < v_uCE_uB5))))))) ∧ (exists (v_uCE_uB5_0 : ℝ), (((v_uCE_uB5_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5_0 > 0)) ∧ (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (exists (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ E)) ∧ (x_2 ∈ E)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) ∧ (|(((f x_1) - (f x_2)))| ≥ v_uCE_uB5_0)))))))) → ((ContinuousOn f E) ∧ (Not (UniformContinuousOn f E))) := by
  sorry
