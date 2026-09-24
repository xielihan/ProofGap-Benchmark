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

-- exercise: exercise_409

theorem proof_gap_exercise_409_1
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) = (((1 + (6 * x)) + (11 * (x ^ (2 : ℕ)))) + (6 * (x ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_409_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) = (((1 + (6 * x)) + (11 * (x ^ (2 : ℕ)))) + (6 * (x ^ (3 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) - 1) /. x) = ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_409_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) = (((1 + (6 * x)) + (11 * (x ^ (2 : ℕ)))) + (6 * (x ^ (3 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) - 1) /. x) = ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) - 1) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_409_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) = (((1 + (6 * x)) + (11 * (x ^ (2 : ℕ)))) + (6 * (x ^ (3 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) - 1) /. x) = ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => (((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) - 1) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 6) := by
  sorry

theorem proof_gap_exercise_409_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) = (((1 + (6 * x)) + (11 * (x ^ (2 : ℕ)))) + (6 * (x ^ (3 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) - 1) /. x) = ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => (((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) - 1) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))))))
  (h4 : Tendsto (fun x : ℝ => ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 6))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((6 + (11 * x)) + (6 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((((1 + x) * (1 + (2 * x))) * (1 + (3 * x))) - 1) /. x)) (𝓝[≠] 0) (𝓝 6) := by
  sorry
