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

-- exercise: exercise_421

theorem proof_gap_exercise_421_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) ∧ (x ≠ (-(2 : ℝ)))) → ((((((x ^ (3 : ℕ)) - (2 * (x ^ (2 : ℕ)))) - (4 * x)) + 8) /. (((x ^ (4 : ℕ)) - (8 * (x ^ (2 : ℕ)))) + 16)) = ((((x - 2) ^ (2 : ℕ)) * (x + 2)) /. (((x - 2) ^ (2 : ℕ)) * ((x + 2) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_421_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) ∧ (x ≠ (-(2 : ℝ)))) → ((((((x ^ (3 : ℕ)) - (2 * (x ^ (2 : ℕ)))) - (4 * x)) + 8) /. (((x ^ (4 : ℕ)) - (8 * (x ^ (2 : ℕ)))) + 16)) = ((((x - 2) ^ (2 : ℕ)) * (x + 2)) /. (((x - 2) ^ (2 : ℕ)) * ((x + 2) ^ (2 : ℕ))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. (x + 2))) (𝓝[≠] 2) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) - (2 * (x ^ (2 : ℕ)))) - (4 * x)) + 8) /. (((x ^ (4 : ℕ)) - (8 * (x ^ (2 : ℕ)))) + 16))) (𝓝[≠] 2) (𝓝 ((𝓝[≠] 2).limUnder (fun x : ℝ => (1 /. (x + 2))))))) := by
  sorry

theorem proof_gap_exercise_421_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) ∧ (x ≠ (-(2 : ℝ)))) → ((((((x ^ (3 : ℕ)) - (2 * (x ^ (2 : ℕ)))) - (4 * x)) + 8) /. (((x ^ (4 : ℕ)) - (8 * (x ^ (2 : ℕ)))) + 16)) = ((((x - 2) ^ (2 : ℕ)) * (x + 2)) /. (((x - 2) ^ (2 : ℕ)) * ((x + 2) ^ (2 : ℕ))))))))
  (h2 : Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) - (2 * (x ^ (2 : ℕ)))) - (4 * x)) + 8) /. (((x ^ (4 : ℕ)) - (8 * (x ^ (2 : ℕ)))) + 16))) (𝓝[≠] 2) (𝓝 ((𝓝[≠] 2).limUnder (fun x : ℝ => (1 /. (x + 2))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. (x + 2))) (𝓝[≠] 2) (𝓝 L))
  : Tendsto (fun x : ℝ => (1 /. (x + 2))) (𝓝[≠] 2) (𝓝 (1 /. 4)) := by
  sorry

theorem proof_gap_exercise_421_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) ∧ (x ≠ (-(2 : ℝ)))) → ((((((x ^ (3 : ℕ)) - (2 * (x ^ (2 : ℕ)))) - (4 * x)) + 8) /. (((x ^ (4 : ℕ)) - (8 * (x ^ (2 : ℕ)))) + 16)) = ((((x - 2) ^ (2 : ℕ)) * (x + 2)) /. (((x - 2) ^ (2 : ℕ)) * ((x + 2) ^ (2 : ℕ))))))))
  (h2 : Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) - (2 * (x ^ (2 : ℕ)))) - (4 * x)) + 8) /. (((x ^ (4 : ℕ)) - (8 * (x ^ (2 : ℕ)))) + 16))) (𝓝[≠] 2) (𝓝 ((𝓝[≠] 2).limUnder (fun x : ℝ => (1 /. (x + 2))))))
  (h3 : Tendsto (fun x : ℝ => (1 /. (x + 2))) (𝓝[≠] 2) (𝓝 (1 /. 4)))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. (x + 2))) (𝓝[≠] 2) (𝓝 L))
  : Tendsto (fun x : ℝ => (((((x ^ (3 : ℕ)) - (2 * (x ^ (2 : ℕ)))) - (4 * x)) + 8) /. (((x ^ (4 : ℕ)) - (8 * (x ^ (2 : ℕ)))) + 16))) (𝓝[≠] 2) (𝓝 (1 /. 4)) := by
  sorry
