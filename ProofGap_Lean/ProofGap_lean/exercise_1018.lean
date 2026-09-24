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

-- exercise: exercise_1018

theorem proof_gap_exercise_1018_1
  : (forall (f : (ℝ -> ℝ)), (True → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a))))) := by
  sorry

theorem proof_gap_exercise_1018_2
  (h1 : (forall (f : (ℝ -> ℝ)), (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a)))))
  (h2 : f = (fun (x : ℝ) => (SignType.sign x : ℝ)))
  (h3 : a = 0)
  : Not (ContinuousAt f 0) := by
  sorry

theorem proof_gap_exercise_1018_3
  (h1 : (forall (f : (ℝ -> ℝ)), (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a)))))
  (h2 : f = (fun (x : ℝ) => (SignType.sign x : ℝ)))
  (h3 : a = 0)
  (h4 : Not (ContinuousAt f 0))
  : (forall (h : ℝ), (((h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0)) → (((((f (0 + h)) - (f 0)) /. h) = ((|(h)| /. h) /. h)) ∧ (((|(h)| /. h) /. h) = (1 /. |(h)|))))) := by
  sorry

theorem proof_gap_exercise_1018_4
  (h1 : (forall (f : (ℝ -> ℝ)), (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a)))))
  (h2 : f = (fun (x : ℝ) => (SignType.sign x : ℝ)))
  (h3 : a = 0)
  (h4 : Not (ContinuousAt f 0))
  (h5 : (forall (h : ℝ), (((h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0)) → (((((f (0 + h)) - (f 0)) /. h) = ((|(h)| /. h) /. h)) ∧ (((|(h)| /. h) /. h) = (1 /. |(h)|))))))
  : Tendsto (fun h : ℝ => ((((f (0 + h)) - (f 0)) /. h) : EReal)) (𝓝[≠] 0) (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_1018_5
  (h1 : (forall (f : (ℝ -> ℝ)), (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a)))))
  (h2 : f = (fun (x : ℝ) => (SignType.sign x : ℝ)))
  (h3 : a = 0)
  (h4 : Not (ContinuousAt f 0))
  (h5 : (forall (h : ℝ), (((h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0)) → (((((f (0 + h)) - (f 0)) /. h) = ((|(h)| /. h) /. h)) ∧ (((|(h)| /. h) /. h) = (1 /. |(h)|))))))
  (h6 : Tendsto (fun h : ℝ => ((((f (0 + h)) - (f 0)) /. h) : EReal)) (𝓝[≠] 0) (𝓝 ⊤))
  : (forall (f : (ℝ -> ℝ)) (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a))) := by
  sorry

theorem proof_gap_exercise_1018_6
  (h1 : (forall (f : (ℝ -> ℝ)), (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a)))))
  (h2 : f = (fun (x : ℝ) => (SignType.sign x : ℝ)))
  (h3 : a = 0)
  (h4 : Not (ContinuousAt f 0))
  (h5 : (forall (h : ℝ), (((h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0)) → (((((f (0 + h)) - (f 0)) /. h) = ((|(h)| /. h) /. h)) ∧ (((|(h)| /. h) /. h) = (1 /. |(h)|))))))
  (h6 : Tendsto (fun h : ℝ => ((((f (0 + h)) - (f 0)) /. h) : EReal)) (𝓝[≠] 0) (𝓝 ⊤))
  (h7 : (forall (f : (ℝ -> ℝ)) (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a))))
  : (exists (f : (ℝ -> ℝ)) (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (Not (ContinuousAt f a))) ∧ (Tendsto (fun h : ℝ => ((((f (a + h)) - (f a)) /. h) : EReal)) (𝓝[≠] 0) (𝓝 ⊤)))) := by
  sorry

theorem proof_gap_exercise_1018_7
  (h1 : (forall (f : (ℝ -> ℝ)), (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a)))))
  (h2 : f = (fun (x : ℝ) => (SignType.sign x : ℝ)))
  (h3 : a = 0)
  (h4 : Not (ContinuousAt f 0))
  (h5 : (forall (h : ℝ), (((h ∈ (Set.univ : Set ℝ)) ∧ (h ≠ 0)) → (((((f (0 + h)) - (f 0)) /. h) = ((|(h)| /. h) /. h)) ∧ (((|(h)| /. h) /. h) = (1 /. |(h)|))))))
  (h6 : Tendsto (fun h : ℝ => ((((f (0 + h)) - (f 0)) /. h) : EReal)) (𝓝[≠] 0) (𝓝 ⊤))
  (h7 : (forall (f : (ℝ -> ℝ)) (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a))))
  (h8 : (exists (f : (ℝ -> ℝ)) (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (Not (ContinuousAt f a))) ∧ (Tendsto (fun h : ℝ => ((((f (a + h)) - (f a)) /. h) : EReal)) (𝓝[≠] 0) (𝓝 ⊤)))))
  : (forall (f : (ℝ -> ℝ)) (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (DifferentiableAt ℝ f a)) → (ContinuousAt f a))) ∧ (exists (f : (ℝ -> ℝ)) (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (Not (ContinuousAt f a))) ∧ (Tendsto (fun h : ℝ => ((((f (a + h)) - (f a)) /. h) : EReal)) (𝓝[≠] 0) (𝓝 ⊤)))) := by
  sorry
