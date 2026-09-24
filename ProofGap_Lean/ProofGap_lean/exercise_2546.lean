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

-- exercise: exercise_2546

theorem proof_gap_exercise_2546_1
  (S : (ℕ -> ℝ))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (i - 1)) /. ((2 : ℕ) ^ (i - 1))))))) := by
  sorry

theorem proof_gap_exercise_2546_2
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (i - 1)) /. ((2 : ℕ) ^ (i - 1))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((1 - (((-(1 : ℤ)) ^ n) /. ((2 : ℕ) ^ n))) /. (1 + (1 /. 2)))))) := by
  sorry

theorem proof_gap_exercise_2546_3
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (i - 1)) /. ((2 : ℕ) ^ (i - 1))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((1 - (((-(1 : ℤ)) ^ n) /. ((2 : ℕ) ^ n))) /. (1 + (1 /. 2)))))))
  : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (1 /. (1 + (1 /. 2)))) := by
  sorry

theorem proof_gap_exercise_2546_4
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (i - 1)) /. ((2 : ℕ) ^ (i - 1))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((1 - (((-(1 : ℤ)) ^ n) /. ((2 : ℕ) ^ n))) /. (1 + (1 /. 2)))))))
  (h3 : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (1 /. (1 + (1 /. 2)))))
  : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (2 /. 3)) := by
  sorry

theorem proof_gap_exercise_2546_5
  (S : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, (((-(1 : ℤ)) ^ (i - 1)) /. ((2 : ℕ) ^ (i - 1))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((1 - (((-(1 : ℤ)) ^ n) /. ((2 : ℕ) ^ n))) /. (1 + (1 /. 2)))))))
  (h3 : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (1 /. (1 + (1 /. 2)))))
  (h4 : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (2 /. 3)))
  : HasSum (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n - 1)) /. ((2 : ℕ) ^ (n - 1))) else 0) (2 /. 3) := by
  sorry
