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

-- exercise: exercise_426

theorem proof_gap_exercise_426_1
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : x = (a + y))
  : (Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_426_2
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : x = (a + y))
  (h5 : (Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)))
  : (x ≠ a) → (y ≠ 0) := by
  sorry

theorem proof_gap_exercise_426_3
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : x = (a + y))
  (h5 : (Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)))
  (h6 : (x ≠ a) → (y ≠ 0))
  : (∃ L : ℝ, Tendsto (fun y : ℝ => (((((a + y) ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * y)) /. (y ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((x ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * (x - a))) /. ((x - a) ^ (2 : ℕ)))) (𝓝[≠] a) (𝓝 ((𝓝[≠] 0).limUnder (fun y : ℝ => (((((a + y) ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * y)) /. (y ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_426_4
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n > 0)
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : x = (a + y))
  (h5 : (Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)))
  (h6 : (x ≠ a) → (y ≠ 0))
  (h7 : Tendsto (fun x : ℝ => ((((x ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * (x - a))) /. ((x - a) ^ (2 : ℕ)))) (𝓝[≠] a) (𝓝 ((𝓝[≠] 0).limUnder (fun y : ℝ => (((((a + y) ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * y)) /. (y ^ (2 : ℕ)))))))
  (h8 : y ≠ 0)
  (h9 : ∃ L : ℝ, Tendsto (fun y : ℝ => (((((a + y) ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * y)) /. (y ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (((((a + y) ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * y)) /. (y ^ (2 : ℕ))) = (∑ k ∈ Finset.Icc (2 : ℕ) n, (((Nat.choose n k) * (a ^ (n - k))) * (y ^ (k - 2)))) := by
  sorry

theorem proof_gap_exercise_426_5
  (a : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : n > 0)
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : x = (a + y))
  (h5 : (Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a)) → (Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0)))
  (h6 : (x ≠ a) → (y ≠ 0))
  (h7 : Tendsto (fun x : ℝ => ((((x ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * (x - a))) /. ((x - a) ^ (2 : ℕ)))) (𝓝[≠] a) (𝓝 ((𝓝[≠] 0).limUnder (fun y : ℝ => (((((a + y) ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * y)) /. (y ^ (2 : ℕ)))))))
  (h8 : (((((a + y) ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * y)) /. (y ^ (2 : ℕ))) = (∑ k ∈ Finset.Icc (2 : ℕ) n, (((Nat.choose n k) * (a ^ (n - k))) * (y ^ (k - 2)))))
  (h9 : n ≥ 2)
  (h10 : ∃ L : ℝ, Tendsto (fun y : ℝ => (((((a + y) ^ n) - (a ^ n)) - ((n * (a ^ (n - 1))) * y)) /. (y ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun y : ℝ => (∑ k ∈ Finset.Icc (2 : ℕ) n, (((Nat.choose n k) * (a ^ (n - k))) * (y ^ (k - 2))))) (𝓝[≠] 0) (𝓝 (((n * (n - 1)) /. 2) * (a ^ (n - 2)))) := by
  sorry
