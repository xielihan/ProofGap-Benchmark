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

-- exercise: exercise_739

theorem proof_gap_exercise_739_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((f x) = (1 /. (1 - x))))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Tendsto (fun x : ℝ => ((f x) : EReal)) (𝓝[>] 1) (𝓝 ⊥)))) := by
  sorry

theorem proof_gap_exercise_739_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((f x) = (1 /. (1 - x))))))
  (h2 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Tendsto (fun x : ℝ => ((f x) : EReal)) (𝓝[>] 1) (𝓝 ⊥)))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Tendsto (fun x : ℝ => ((f x) : EReal)) (𝓝[<] 1) (𝓝 ⊤)))) := by
  sorry

theorem proof_gap_exercise_739_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((f x) = (1 /. (1 - x))))))
  (h2 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Tendsto (fun x : ℝ => ((f x) : EReal)) (𝓝[>] 1) (𝓝 ⊥)))))
  (h3 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Tendsto (fun x : ℝ => ((f x) : EReal)) (𝓝[<] 1) (𝓝 ⊤)))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Not (ContinuousAt f 1)))) := by
  sorry

theorem proof_gap_exercise_739_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((f x) = (1 /. (1 - x))))))
  (h2 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Tendsto (fun x : ℝ => ((f x) : EReal)) (𝓝[>] 1) (𝓝 ⊥)))))
  (h3 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Tendsto (fun x : ℝ => ((f x) : EReal)) (𝓝[<] 1) (𝓝 ⊤)))))
  (h4 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Not (ContinuousAt f 1)))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ ((f (1 : ℝ)) = a)) → (Not (ContinuousAt f 1)))) := by
  sorry
