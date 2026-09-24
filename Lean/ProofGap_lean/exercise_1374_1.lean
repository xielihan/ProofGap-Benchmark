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

-- exercise: exercise_1374_1

theorem proof_gap_exercise_1374_1_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.sin x_1) ≠ 0)) → ((((x_1 ^ (2 : ℕ)) * (Real.sin (1 /. x_1))) /. (Real.sin x_1)) = (((x_1 /. (Real.sin x_1)) * x_1) * (Real.sin (1 /. x_1)))))) := by
  sorry

theorem proof_gap_exercise_1374_1_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.sin x_1) ≠ 0)) → ((((x_1 ^ (2 : ℕ)) * (Real.sin (1 /. x_1))) /. (Real.sin x_1)) = (((x_1 /. (Real.sin x_1)) * x_1) * (Real.sin (1 /. x_1)))))))
  : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.cos x_1) ≠ 0)) → (((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) * (Real.sin (1 /. t)))) x_1) /. (iteratedDeriv 1 (fun t => (Real.sin t)) x_1)) = ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))))) := by
  sorry

theorem proof_gap_exercise_1374_1_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.sin x_1) ≠ 0)) → ((((x_1 ^ (2 : ℕ)) * (Real.sin (1 /. x_1))) /. (Real.sin x_1)) = (((x_1 /. (Real.sin x_1)) * x_1) * (Real.sin (1 /. x_1)))))))
  (h3 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.cos x_1) ≠ 0)) → (((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) * (Real.sin (1 /. t)))) x_1) /. (iteratedDeriv 1 (fun t => (Real.sin t)) x_1)) = ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))))))
  : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x_1 : ℝ => ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))) (𝓝[≠] 0) (𝓝 L)))) := by
  sorry

theorem proof_gap_exercise_1374_1_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.sin x_1) ≠ 0)) → ((((x_1 ^ (2 : ℕ)) * (Real.sin (1 /. x_1))) /. (Real.sin x_1)) = (((x_1 /. (Real.sin x_1)) * x_1) * (Real.sin (1 /. x_1)))))))
  (h3 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.cos x_1) ≠ 0)) → (((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) * (Real.sin (1 /. t)))) x_1) /. (iteratedDeriv 1 (fun t => (Real.sin t)) x_1)) = ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))))))
  (h4 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x_1 : ℝ => ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))) (𝓝[≠] 0) (𝓝 L)))))
  : Tendsto (fun x_1 : ℝ => (x_1 /. (Real.sin x_1))) (𝓝[≠] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_1374_1_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.sin x_1) ≠ 0)) → ((((x_1 ^ (2 : ℕ)) * (Real.sin (1 /. x_1))) /. (Real.sin x_1)) = (((x_1 /. (Real.sin x_1)) * x_1) * (Real.sin (1 /. x_1)))))))
  (h3 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.cos x_1) ≠ 0)) → (((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) * (Real.sin (1 /. t)))) x_1) /. (iteratedDeriv 1 (fun t => (Real.sin t)) x_1)) = ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))))))
  (h4 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x_1 : ℝ => ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))) (𝓝[≠] 0) (𝓝 L)))))
  (h5 : Tendsto (fun x_1 : ℝ => (x_1 /. (Real.sin x_1))) (𝓝[≠] 0) (𝓝 1))
  : Tendsto (fun x_1 : ℝ => (x_1 * (Real.sin (1 /. x_1)))) (𝓝[≠] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_1374_1_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.sin x_1) ≠ 0)) → ((((x_1 ^ (2 : ℕ)) * (Real.sin (1 /. x_1))) /. (Real.sin x_1)) = (((x_1 /. (Real.sin x_1)) * x_1) * (Real.sin (1 /. x_1)))))))
  (h3 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ 0)) ∧ ((Real.cos x_1) ≠ 0)) → (((iteratedDeriv 1 (fun t => ((t ^ (2 : ℕ)) * (Real.sin (1 /. t)))) x_1) /. (iteratedDeriv 1 (fun t => (Real.sin t)) x_1)) = ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))))))
  (h4 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x_1 : ℝ => ((((2 * x_1) * (Real.sin (1 /. x_1))) - (Real.cos (1 /. x_1))) /. (Real.cos x_1))) (𝓝[≠] 0) (𝓝 L)))))
  (h5 : Tendsto (fun x_1 : ℝ => (x_1 /. (Real.sin x_1))) (𝓝[≠] 0) (𝓝 1))
  (h6 : Tendsto (fun x_1 : ℝ => (x_1 * (Real.sin (1 /. x_1)))) (𝓝[≠] 0) (𝓝 0))
  : Tendsto (fun x_1 : ℝ => (((x_1 ^ (2 : ℕ)) * (Real.sin (1 /. x_1))) /. (Real.sin x_1))) (𝓝[≠] 0) (𝓝 0) := by
  sorry
