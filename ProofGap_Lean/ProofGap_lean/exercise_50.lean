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

-- exercise: exercise_50

theorem proof_gap_exercise_50_1
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : |(a)| < 1)
  (h4 : |(b)| < 1)
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((∑ k ∈ Finset.Icc (0 : ℕ) n, (a ^ k)) /. (∑ k ∈ Finset.Icc (0 : ℕ) n, (b ^ k))) = (((1 - (a ^ (n + 1))) /. (1 - a)) /. ((1 - (b ^ (n + 1))) /. (1 - b)))))) := by
  sorry

theorem proof_gap_exercise_50_2
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : |(a)| < 1)
  (h4 : |(b)| < 1)
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((∑ k ∈ Finset.Icc (0 : ℕ) n, (a ^ k)) /. (∑ k ∈ Finset.Icc (0 : ℕ) n, (b ^ k))) = (((1 - (a ^ (n + 1))) /. (1 - a)) /. ((1 - (b ^ (n + 1))) /. (1 - b)))))))
  : Tendsto (fun n : ℕ => (Real.rpow a (n + 1))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_50_3
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : |(a)| < 1)
  (h4 : |(b)| < 1)
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((∑ k ∈ Finset.Icc (0 : ℕ) n, (a ^ k)) /. (∑ k ∈ Finset.Icc (0 : ℕ) n, (b ^ k))) = (((1 - (a ^ (n + 1))) /. (1 - a)) /. ((1 - (b ^ (n + 1))) /. (1 - b)))))))
  (h6 : Tendsto (fun n : ℕ => (Real.rpow a (n + 1))) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => (Real.rpow b (n + 1))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_50_4
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : |(a)| < 1)
  (h4 : |(b)| < 1)
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (((∑ k ∈ Finset.Icc (0 : ℕ) n, (a ^ k)) /. (∑ k ∈ Finset.Icc (0 : ℕ) n, (b ^ k))) = (((1 - (a ^ (n + 1))) /. (1 - a)) /. ((1 - (b ^ (n + 1))) /. (1 - b)))))))
  (h6 : Tendsto (fun n : ℕ => (Real.rpow a (n + 1))) atTop (𝓝 0))
  (h7 : Tendsto (fun n : ℕ => (Real.rpow b (n + 1))) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => ((∑ k ∈ Finset.Icc (0 : ℕ) n, (a ^ k)) /. (∑ k ∈ Finset.Icc (0 : ℕ) n, (b ^ k)))) atTop (𝓝 ((1 - b) /. (1 - a))) := by
  sorry
