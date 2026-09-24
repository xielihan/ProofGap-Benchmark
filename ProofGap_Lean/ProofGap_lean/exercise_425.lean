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

-- exercise: exercise_425

theorem proof_gap_exercise_425_1
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((((x ^ m) - 1) /. ((x ^ n) - 1)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ i)) /. (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ j)))))) := by
  sorry

theorem proof_gap_exercise_425_2
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((((x ^ m) - 1) /. ((x ^ n) - 1)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ i)) /. (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ j)))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((∑ i ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ i)) /. (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ j)))) (𝓝[≠] 1) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((x ^ m) - 1) /. ((x ^ n) - 1))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => ((∑ i ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ i)) /. (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ j)))))))) := by
  sorry

theorem proof_gap_exercise_425_3
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((x ^ n) ≠ 1)) → ((((x ^ m) - 1) /. ((x ^ n) - 1)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ i)) /. (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ j)))))))
  (h6 : Tendsto (fun x : ℝ => (((x ^ m) - 1) /. ((x ^ n) - 1))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => ((∑ i ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ i)) /. (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ j)))))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((∑ i ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ i)) /. (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ j)))) (𝓝[≠] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => ((∑ i ∈ Finset.Icc (0 : ℕ) (m - 1), (x ^ i)) /. (∑ j ∈ Finset.Icc (0 : ℕ) (n - 1), (x ^ j)))) (𝓝[≠] 1) (𝓝 (m /. n)) := by
  sorry
