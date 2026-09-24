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

-- exercise: exercise_179

theorem proof_gap_exercise_179_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  : ContinuousOn y (Set.Ioo 10 1000) := by
  sorry

theorem proof_gap_exercise_179_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  : MonotoneOn y (Set.Ioo 10 1000) := by
  sorry

theorem proof_gap_exercise_179_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  (h3 : MonotoneOn y (Set.Ioo 10 1000))
  : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 (Real.logb 10 (10 : ℝ))) := by
  sorry

theorem proof_gap_exercise_179_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  (h3 : MonotoneOn y (Set.Ioo 10 1000))
  (h4 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 (Real.logb 10 (10 : ℝ))))
  : (Real.logb 10 (10 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_179_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  (h3 : MonotoneOn y (Set.Ioo 10 1000))
  (h4 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 (Real.logb 10 (10 : ℝ))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_179_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  (h3 : MonotoneOn y (Set.Ioo 10 1000))
  (h4 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 (Real.logb 10 (10 : ℝ))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 1))
  : Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1000) (𝓝 (Real.logb 10 (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_179_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  (h3 : MonotoneOn y (Set.Ioo 10 1000))
  (h4 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 (Real.logb 10 (10 : ℝ))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 1))
  (h7 : Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1000) (𝓝 (Real.logb 10 (1000 : ℝ))))
  : (Real.logb 10 (1000 : ℝ)) = 3 := by
  sorry

theorem proof_gap_exercise_179_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  (h3 : MonotoneOn y (Set.Ioo 10 1000))
  (h4 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 (Real.logb 10 (10 : ℝ))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 1))
  (h7 : Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1000) (𝓝 (Real.logb 10 (1000 : ℝ))))
  (h8 : (Real.logb 10 (1000 : ℝ)) = 3)
  : Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1000) (𝓝 3) := by
  sorry

theorem proof_gap_exercise_179_9
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  (h3 : MonotoneOn y (Set.Ioo 10 1000))
  (h4 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 (Real.logb 10 (10 : ℝ))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 1))
  (h7 : Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1000) (𝓝 (Real.logb 10 (1000 : ℝ))))
  (h8 : (Real.logb 10 (1000 : ℝ)) = 3)
  (h9 : Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1000) (𝓝 3))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (10 < x)) ∧ (x < 1000)) → ((1 < (y x)) ∧ ((y x) < 3)))) := by
  sorry

theorem proof_gap_exercise_179_10
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((y x) = (Real.logb 10 x)))))
  (h2 : ContinuousOn y (Set.Ioo 10 1000))
  (h3 : MonotoneOn y (Set.Ioo 10 1000))
  (h4 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 (Real.logb 10 (10 : ℝ))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : Tendsto (fun x : ℝ => (y x)) (𝓝[>] 10) (𝓝 1))
  (h7 : Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1000) (𝓝 (Real.logb 10 (1000 : ℝ))))
  (h8 : (Real.logb 10 (1000 : ℝ)) = 3)
  (h9 : Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1000) (𝓝 3))
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (10 < x)) ∧ (x < 1000)) → ((1 < (y x)) ∧ ((y x) < 3)))))
  : (y '' (Set.Ioo 10 1000)) = Set.Ioo 1 3 := by
  sorry
