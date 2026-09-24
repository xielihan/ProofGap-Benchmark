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

-- exercise: exercise_1374_2

theorem proof_gap_exercise_1374_2_1
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((x + (Real.sin x)) ≠ 0)) → (((x - (Real.sin x)) /. (x + (Real.sin x))) = ((1 - ((Real.sin x) /. x)) /. (1 + ((Real.sin x) /. x)))))) := by
  sorry

theorem proof_gap_exercise_1374_2_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((x + (Real.sin x)) ≠ 0)) → (((x - (Real.sin x)) /. (x + (Real.sin x))) = ((1 - ((Real.sin x) /. x)) /. (1 + ((Real.sin x) /. x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos x)) ≠ 0)) → (((iteratedDeriv 1 (fun t => (t - (Real.sin t))) x) /. (iteratedDeriv 1 (fun t => (t + (Real.sin t))) x)) = ((1 - (Real.cos x)) /. (1 + (Real.cos x)))))) := by
  sorry

theorem proof_gap_exercise_1374_2_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((x + (Real.sin x)) ≠ 0)) → (((x - (Real.sin x)) /. (x + (Real.sin x))) = ((1 - ((Real.sin x) /. x)) /. (1 + ((Real.sin x) /. x)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos x)) ≠ 0)) → (((iteratedDeriv 1 (fun t => (t - (Real.sin t))) x) /. (iteratedDeriv 1 (fun t => (t + (Real.sin t))) x)) = ((1 - (Real.cos x)) /. (1 + (Real.cos x)))))))
  : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => ((1 - (Real.cos x)) /. (1 + (Real.cos x)))) atTop (𝓝 L)))) := by
  sorry

theorem proof_gap_exercise_1374_2_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((x + (Real.sin x)) ≠ 0)) → (((x - (Real.sin x)) /. (x + (Real.sin x))) = ((1 - ((Real.sin x) /. x)) /. (1 + ((Real.sin x) /. x)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos x)) ≠ 0)) → (((iteratedDeriv 1 (fun t => (t - (Real.sin t))) x) /. (iteratedDeriv 1 (fun t => (t + (Real.sin t))) x)) = ((1 - (Real.cos x)) /. (1 + (Real.cos x)))))))
  (h3 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => ((1 - (Real.cos x)) /. (1 + (Real.cos x)))) atTop (𝓝 L)))))
  : Tendsto (fun x : ℝ => ((Real.sin x) /. x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_1374_2_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((x + (Real.sin x)) ≠ 0)) → (((x - (Real.sin x)) /. (x + (Real.sin x))) = ((1 - ((Real.sin x) /. x)) /. (1 + ((Real.sin x) /. x)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos x)) ≠ 0)) → (((iteratedDeriv 1 (fun t => (t - (Real.sin t))) x) /. (iteratedDeriv 1 (fun t => (t + (Real.sin t))) x)) = ((1 - (Real.cos x)) /. (1 + (Real.cos x)))))))
  (h3 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => ((1 - (Real.cos x)) /. (1 + (Real.cos x)))) atTop (𝓝 L)))))
  (h4 : Tendsto (fun x : ℝ => ((Real.sin x) /. x)) atTop (𝓝 0))
  : Tendsto (fun x : ℝ => ((1 - ((Real.sin x) /. x)) /. (1 + ((Real.sin x) /. x)))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_1374_2_6
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((x + (Real.sin x)) ≠ 0)) → (((x - (Real.sin x)) /. (x + (Real.sin x))) = ((1 - ((Real.sin x) /. x)) /. (1 + ((Real.sin x) /. x)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((1 + (Real.cos x)) ≠ 0)) → (((iteratedDeriv 1 (fun t => (t - (Real.sin t))) x) /. (iteratedDeriv 1 (fun t => (t + (Real.sin t))) x)) = ((1 - (Real.cos x)) /. (1 + (Real.cos x)))))))
  (h3 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => ((1 - (Real.cos x)) /. (1 + (Real.cos x)))) atTop (𝓝 L)))))
  (h4 : Tendsto (fun x : ℝ => ((Real.sin x) /. x)) atTop (𝓝 0))
  (h5 : Tendsto (fun x : ℝ => ((1 - ((Real.sin x) /. x)) /. (1 + ((Real.sin x) /. x)))) atTop (𝓝 1))
  : Tendsto (fun x : ℝ => ((x - (Real.sin x)) /. (x + (Real.sin x)))) atTop (𝓝 1) := by
  sorry
