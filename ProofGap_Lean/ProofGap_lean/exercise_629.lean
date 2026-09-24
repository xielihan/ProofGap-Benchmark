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

-- exercise: exercise_629

theorem proof_gap_exercise_629_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((1 + (x ^ ((2 : ℕ) ^ k))) = ((1 - (x ^ ((2 : ℕ) ^ (k + 1)))) /. (1 - (x ^ ((2 : ℕ) ^ k))))))) := by
  sorry

theorem proof_gap_exercise_629_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((1 + (x ^ ((2 : ℕ) ^ k))) = ((1 - (x ^ ((2 : ℕ) ^ (k + 1)))) /. (1 - (x ^ ((2 : ℕ) ^ k))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))) := by
  sorry

theorem proof_gap_exercise_629_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((1 + (x ^ ((2 : ℕ) ^ k))) = ((1 - (x ^ ((2 : ℕ) ^ (k + 1)))) /. (1 - (x ^ ((2 : ℕ) ^ k))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_629_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : |(x)| < 1)
  (h3 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((1 + (x ^ ((2 : ℕ) ^ k))) = ((1 - (x ^ ((2 : ℕ) ^ (k + 1)))) /. (1 - (x ^ ((2 : ℕ) ^ k))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k)))) = ((1 - (x ^ ((2 : ℕ) ^ (n + 1)))) /. (1 - x))))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow x (Real.rpow (2 : ℝ) (n + 1)))) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => (∏ k ∈ Finset.Icc (0 : ℕ) n, (1 + (x ^ ((2 : ℕ) ^ k))))) atTop (𝓝 (1 /. (1 - x))) := by
  sorry
