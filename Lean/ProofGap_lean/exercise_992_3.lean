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

-- exercise: exercise_992_3

theorem proof_gap_exercise_992_3_1
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((x ^ n) * (Real.sin (1 /. x)))))))
  (h4 : (f (0 : ℝ)) = 0)
  : (n > 2) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (((n * (x ^ (n - 1))) * (Real.sin (1 /. x))) - ((x ^ (n - 2)) * (Real.cos (1 /. x))))))) := by
  sorry

theorem proof_gap_exercise_992_3_2
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((x ^ n) * (Real.sin (1 /. x)))))))
  (h4 : (f (0 : ℝ)) = 0)
  (h5 : (n > 2) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (((n * (x ^ (n - 1))) * (Real.sin (1 /. x))) - ((x ^ (n - 2)) * (Real.cos (1 /. x))))))))
  : (n > 2) → (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) (𝓝[≠] 0) (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_992_3_3
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((x ^ n) * (Real.sin (1 /. x)))))))
  (h4 : (f (0 : ℝ)) = 0)
  (h5 : (n > 2) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (((n * (x ^ (n - 1))) * (Real.sin (1 /. x))) - ((x ^ (n - 2)) * (Real.cos (1 /. x))))))))
  (h6 : (n > 2) → (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) (𝓝[≠] 0) (𝓝 0)))
  : (n > 2) → ((iteratedDeriv 1 (fun t => f t) 0) = 0) := by
  sorry

theorem proof_gap_exercise_992_3_4
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((x ^ n) * (Real.sin (1 /. x)))))))
  (h4 : (f (0 : ℝ)) = 0)
  (h5 : (n > 2) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (((n * (x ^ (n - 1))) * (Real.sin (1 /. x))) - ((x ^ (n - 2)) * (Real.cos (1 /. x))))))))
  (h6 : (n > 2) → (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) (𝓝[≠] 0) (𝓝 0)))
  (h7 : (n > 2) → ((iteratedDeriv 1 (fun t => f t) 0) = 0))
  : (n > 2) → (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t => f t) 0))) := by
  sorry

theorem proof_gap_exercise_992_3_5
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((x ^ n) * (Real.sin (1 /. x)))))))
  (h4 : (f (0 : ℝ)) = 0)
  (h5 : (n > 2) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (((n * (x ^ (n - 1))) * (Real.sin (1 /. x))) - ((x ^ (n - 2)) * (Real.cos (1 /. x))))))))
  (h6 : (n > 2) → (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) (𝓝[≠] 0) (𝓝 0)))
  (h7 : (n > 2) → ((iteratedDeriv 1 (fun t => f t) 0) = 0))
  (h8 : (n > 2) → (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t => f t) 0))))
  : (n > 2) → (ContinuousAt (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) 0) := by
  sorry

theorem proof_gap_exercise_992_3_6
  (f : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = ((x ^ n) * (Real.sin (1 /. x)))))))
  (h4 : (f (0 : ℝ)) = 0)
  (h5 : (n > 2) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => f t) x) = (((n * (x ^ (n - 1))) * (Real.sin (1 /. x))) - ((x ^ (n - 2)) * (Real.cos (1 /. x))))))))
  (h6 : (n > 2) → (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) (𝓝[≠] 0) (𝓝 0)))
  (h7 : (n > 2) → ((iteratedDeriv 1 (fun t => f t) 0) = 0))
  (h8 : (n > 2) → (Tendsto (fun x : ℝ => (iteratedDeriv 1 (fun t => f t) x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t => f t) 0))))
  (h9 : (n > 2) → (ContinuousAt (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) 0))
  : (n ∈ ({n_1 | (n_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (n_1 > 2)})) ↔ (ContinuousAt (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) 0) := by
  sorry
