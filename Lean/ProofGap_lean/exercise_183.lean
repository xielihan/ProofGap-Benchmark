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

-- exercise: exercise_183

theorem proof_gap_exercise_183_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  : ContinuousOn y (Set.Ioo 0 1) := by
  sorry

theorem proof_gap_exercise_183_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  (h4 : ContinuousOn y (Set.Ioo 0 1))
  : (a < b) → (MonotoneOn y (Set.Ioo 0 1)) := by
  sorry

theorem proof_gap_exercise_183_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  (h4 : ContinuousOn y (Set.Ioo 0 1))
  (h5 : (a < b) → (MonotoneOn y (Set.Ioo 0 1)))
  : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)) := by
  sorry

theorem proof_gap_exercise_183_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  (h4 : ContinuousOn y (Set.Ioo 0 1))
  (h5 : (a < b) → (MonotoneOn y (Set.Ioo 0 1)))
  (h6 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)))
  : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1) (𝓝 b)) := by
  sorry

theorem proof_gap_exercise_183_5
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  (h4 : ContinuousOn y (Set.Ioo 0 1))
  (h5 : (a < b) → (MonotoneOn y (Set.Ioo 0 1)))
  (h6 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1) (𝓝 b)))
  : (a < b) → ((y '' (Set.Ioo 0 1)) = Set.Ioo a b) := by
  sorry

theorem proof_gap_exercise_183_6
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  (h4 : ContinuousOn y (Set.Ioo 0 1))
  (h5 : (a < b) → (MonotoneOn y (Set.Ioo 0 1)))
  (h6 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1) (𝓝 b)))
  (h8 : (a < b) → ((y '' (Set.Ioo 0 1)) = Set.Ioo a b))
  : (b < a) → (AntitoneOn y (Set.Ioo 0 1)) := by
  sorry

theorem proof_gap_exercise_183_7
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  (h4 : ContinuousOn y (Set.Ioo 0 1))
  (h5 : (a < b) → (MonotoneOn y (Set.Ioo 0 1)))
  (h6 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1) (𝓝 b)))
  (h8 : (a < b) → ((y '' (Set.Ioo 0 1)) = Set.Ioo a b))
  (h9 : (b < a) → (AntitoneOn y (Set.Ioo 0 1)))
  : (b < a) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)) := by
  sorry

theorem proof_gap_exercise_183_8
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  (h4 : ContinuousOn y (Set.Ioo 0 1))
  (h5 : (a < b) → (MonotoneOn y (Set.Ioo 0 1)))
  (h6 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1) (𝓝 b)))
  (h8 : (a < b) → ((y '' (Set.Ioo 0 1)) = Set.Ioo a b))
  (h9 : (b < a) → (AntitoneOn y (Set.Ioo 0 1)))
  (h10 : (b < a) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)))
  : (b < a) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1) (𝓝 b)) := by
  sorry

theorem proof_gap_exercise_183_9
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 1))) → ((y x) = (a + ((b - a) * x))))))
  (h4 : ContinuousOn y (Set.Ioo 0 1))
  (h5 : (a < b) → (MonotoneOn y (Set.Ioo 0 1)))
  (h6 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)))
  (h7 : (a < b) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1) (𝓝 b)))
  (h8 : (a < b) → ((y '' (Set.Ioo 0 1)) = Set.Ioo a b))
  (h9 : (b < a) → (AntitoneOn y (Set.Ioo 0 1)))
  (h10 : (b < a) → (Tendsto (fun x : ℝ => (y x)) (𝓝[>] 0) (𝓝 a)))
  (h11 : (b < a) → (Tendsto (fun x : ℝ => (y x)) (𝓝[<] 1) (𝓝 b)))
  : (b < a) → ((y '' (Set.Ioo 0 1)) = Set.Ioo b a) := by
  sorry
