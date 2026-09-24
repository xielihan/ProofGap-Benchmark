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

-- exercise: exercise_180

theorem proof_gap_exercise_180_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((1 /. Real.pi) * ((Real.pi /. 2) - (Real.arctan x)))))))
  : ContinuousOn y Set.univ := by
  sorry

theorem proof_gap_exercise_180_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((1 /. Real.pi) * ((Real.pi /. 2) - (Real.arctan x)))))))
  (h2 : ContinuousOn y Set.univ)
  : AntitoneOn y Set.univ := by
  sorry

theorem proof_gap_exercise_180_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((1 /. Real.pi) * ((Real.pi /. 2) - (Real.arctan x)))))))
  (h2 : ContinuousOn y Set.univ)
  (h3 : AntitoneOn y Set.univ)
  : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atBot (𝓝 Real.pi) := by
  sorry

theorem proof_gap_exercise_180_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((1 /. Real.pi) * ((Real.pi /. 2) - (Real.arctan x)))))))
  (h2 : ContinuousOn y Set.univ)
  (h3 : AntitoneOn y Set.univ)
  (h4 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atBot (𝓝 Real.pi))
  : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_180_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((1 /. Real.pi) * ((Real.pi /. 2) - (Real.arctan x)))))))
  (h2 : ContinuousOn y Set.univ)
  (h3 : AntitoneOn y Set.univ)
  (h4 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atBot (𝓝 Real.pi))
  (h5 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atTop (𝓝 0))
  : Tendsto (fun x : ℝ => (y x)) atBot (𝓝 1) := by
  sorry

theorem proof_gap_exercise_180_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((1 /. Real.pi) * ((Real.pi /. 2) - (Real.arctan x)))))))
  (h2 : ContinuousOn y Set.univ)
  (h3 : AntitoneOn y Set.univ)
  (h4 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atBot (𝓝 Real.pi))
  (h5 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atTop (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (y x)) atBot (𝓝 1))
  : Tendsto (fun x : ℝ => (y x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_180_7
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((1 /. Real.pi) * ((Real.pi /. 2) - (Real.arctan x)))))))
  (h2 : ContinuousOn y Set.univ)
  (h3 : AntitoneOn y Set.univ)
  (h4 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atBot (𝓝 Real.pi))
  (h5 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atTop (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (y x)) atBot (𝓝 1))
  (h7 : Tendsto (fun x : ℝ => (y x)) atTop (𝓝 0))
  : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (((y x) = 0) ∨ ((y x) = 1)))) := by
  sorry

theorem proof_gap_exercise_180_8
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((1 /. Real.pi) * ((Real.pi /. 2) - (Real.arctan x)))))))
  (h2 : ContinuousOn y Set.univ)
  (h3 : AntitoneOn y Set.univ)
  (h4 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atBot (𝓝 Real.pi))
  (h5 : Tendsto (fun x : ℝ => ((Real.pi /. 2) - (Real.arctan x))) atTop (𝓝 0))
  (h6 : Tendsto (fun x : ℝ => (y x)) atBot (𝓝 1))
  (h7 : Tendsto (fun x : ℝ => (y x)) atTop (𝓝 0))
  (h8 : Not (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (((y x) = 0) ∨ ((y x) = 1)))))
  : (y '' Set.univ) = Set.Ioo 0 1 := by
  sorry
