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

-- exercise: exercise_626

theorem proof_gap_exercise_626_1
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((f x_1) /. x_1) = (((((f x_1) - ((k * x_1) + b)) /. x_1) + k) + (b /. x_1))))) := by
  sorry

theorem proof_gap_exercise_626_2
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((f x_1) /. x_1) = (((((f x_1) - ((k * x_1) + b)) /. x_1) + k) + (b /. x_1))))))
  : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)) := by
  sorry

theorem proof_gap_exercise_626_3
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((f x_1) /. x_1) = (((((f x_1) - ((k * x_1) + b)) /. x_1) + k) + (b /. x_1))))))
  (h5 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)))
  : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atTop (𝓝 b)) := by
  sorry

theorem proof_gap_exercise_626_4
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((f x_1) /. x_1) = (((((f x_1) - ((k * x_1) + b)) /. x_1) + k) + (b /. x_1))))))
  (h5 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)))
  (h6 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atTop (𝓝 b)))
  : (Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)) → ((Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atTop (𝓝 b)) → (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0))) := by
  sorry

theorem proof_gap_exercise_626_5
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((f x_1) /. x_1) = (((((f x_1) - ((k * x_1) + b)) /. x_1) + k) + (b /. x_1))))))
  (h5 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)))
  (h6 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atTop (𝓝 b)))
  (h7 : (Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)) → ((Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atTop (𝓝 b)) → (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0))))
  : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atBot (𝓝 0)) ↔ ((Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atBot (𝓝 k)) ∧ (Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atBot (𝓝 b))) := by
  sorry

theorem proof_gap_exercise_626_6
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (b : ℝ)
  (x : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → (((f x_1) /. x_1) = (((((f x_1) - ((k * x_1) + b)) /. x_1) + k) + (b /. x_1))))))
  (h5 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)))
  (h6 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) → (Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atTop (𝓝 b)))
  (h7 : (Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)) → ((Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atTop (𝓝 b)) → (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0))))
  (h8 : (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atBot (𝓝 0)) ↔ ((Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atBot (𝓝 k)) ∧ (Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atBot (𝓝 b))))
  : ((Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) ↔ ((Tendsto (fun x_1 : ℝ => ((f x_1) /. x_1)) atTop (𝓝 k)) ∧ (Tendsto (fun x_1 : ℝ => ((f x_1) - (k * x_1))) atTop (𝓝 b)))) → (Tendsto (fun x_1 : ℝ => ((f x_1) - ((k * x_1) + b))) atTop (𝓝 0)) := by
  sorry
