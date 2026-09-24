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

-- exercise: exercise_427

theorem proof_gap_exercise_427_1
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : x = (1 + y))
  : (Tendsto (fun x : ℝ => x) (𝓝[≠] 1) (𝓝 1)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_427_2
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : x = (1 + y))
  (h4 : (Tendsto (fun x : ℝ => x) (𝓝[≠] 1) (𝓝 1)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)))
  : (x ≠ 1) → (y ≠ 0) := by
  sorry

theorem proof_gap_exercise_427_3
  (n : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : x = (1 + y))
  (h4 : (Tendsto (fun x : ℝ => x) (𝓝[≠] 1) (𝓝 1)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)))
  (h5 : (x ≠ 1) → (y ≠ 0))
  : (∃ L : ℝ, Tendsto (fun y : ℝ => (((((1 + y) ^ (n + 1)) - ((n + 1) * (1 + y))) + n) /. (y ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((x ^ (n + 1)) - ((n + 1) * x)) + n) /. ((x - 1) ^ (2 : ℕ)))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 0).limUnder (fun y : ℝ => (((((1 + y) ^ (n + 1)) - ((n + 1) * (1 + y))) + n) /. (y ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_427_4
  (n : ℕ)
  (h1 : n > 0)
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : x = (1 + y))
  (h4 : (Tendsto (fun x : ℝ => x) (𝓝[≠] 1) (𝓝 1)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)))
  (h5 : (x ≠ 1) → (y ≠ 0))
  (h6 : Tendsto (fun x : ℝ => ((((x ^ (n + 1)) - ((n + 1) * x)) + n) /. ((x - 1) ^ (2 : ℕ)))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 0).limUnder (fun y : ℝ => (((((1 + y) ^ (n + 1)) - ((n + 1) * (1 + y))) + n) /. (y ^ (2 : ℕ)))))))
  (h7 : y ≠ 0)
  (h8 : ∃ L : ℝ, Tendsto (fun y : ℝ => (((((1 + y) ^ (n + 1)) - ((n + 1) * (1 + y))) + n) /. (y ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (((((1 + y) ^ (n + 1)) - ((n + 1) * (1 + y))) + n) /. (y ^ (2 : ℕ))) = (∑ k ∈ Finset.Icc (2 : ℕ) (n + 1), ((Nat.choose (n + 1) k) * (y ^ (k - 2)))) := by
  sorry

theorem proof_gap_exercise_427_5
  (n : ℕ)
  (h1 : n > 0)
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : x = (1 + y))
  (h4 : (Tendsto (fun x : ℝ => x) (𝓝[≠] 1) (𝓝 1)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)))
  (h5 : (x ≠ 1) → (y ≠ 0))
  (h6 : Tendsto (fun x : ℝ => ((((x ^ (n + 1)) - ((n + 1) * x)) + n) /. ((x - 1) ^ (2 : ℕ)))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 0).limUnder (fun y : ℝ => (((((1 + y) ^ (n + 1)) - ((n + 1) * (1 + y))) + n) /. (y ^ (2 : ℕ)))))))
  (h7 : (((((1 + y) ^ (n + 1)) - ((n + 1) * (1 + y))) + n) /. (y ^ (2 : ℕ))) = (∑ k ∈ Finset.Icc (2 : ℕ) (n + 1), ((Nat.choose (n + 1) k) * (y ^ (k - 2)))))
  (h8 : y ≠ 0)
  (h9 : ∃ L : ℝ, Tendsto (fun y : ℝ => (((((1 + y) ^ (n + 1)) - ((n + 1) * (1 + y))) + n) /. (y ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun y : ℝ => (∑ k ∈ Finset.Icc (2 : ℕ) (n + 1), ((Nat.choose (n + 1) k) * (y ^ (k - 2))))) (𝓝[≠] 0) (𝓝 ((n * (n + 1)) /. 2)) := by
  sorry
