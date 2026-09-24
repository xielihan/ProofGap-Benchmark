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

-- exercise: exercise_3901

theorem proof_gap_exercise_3901_1
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, (∑ j ∈ Finset.Icc (1 : ℕ) n, (((i /. n) * (j /. n)) * (1 /. (n ^ (2 : ℕ)))))) = (((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j))))) := by
  sorry

theorem proof_gap_exercise_3901_2
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, (∑ j ∈ Finset.Icc (1 : ℕ) n, (((i /. n) * (j /. n)) * (1 /. (n ^ (2 : ℕ)))))) = (((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, i) = ((n * (n + 1)) /. 2)))) := by
  sorry

theorem proof_gap_exercise_3901_3
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, (∑ j ∈ Finset.Icc (1 : ℕ) n, (((i /. n) * (j /. n)) * (1 /. (n ^ (2 : ℕ)))))) = (((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, i) = ((n * (n + 1)) /. 2)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ j ∈ Finset.Icc (1 : ℕ) n, j) = ((n * (n + 1)) /. 2)))) := by
  sorry

theorem proof_gap_exercise_3901_4
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, (∑ j ∈ Finset.Icc (1 : ℕ) n, (((i /. n) * (j /. n)) * (1 /. (n ^ (2 : ℕ)))))) = (((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, i) = ((n * (n + 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ j ∈ Finset.Icc (1 : ℕ) n, j) = ((n * (n + 1)) /. 2)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j)) = (((n ^ (2 : ℕ)) * ((n + 1) ^ (2 : ℕ))) /. (4 * (n ^ (4 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3901_5
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, (∑ j ∈ Finset.Icc (1 : ℕ) n, (((i /. n) * (j /. n)) * (1 /. (n ^ (2 : ℕ)))))) = (((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, i) = ((n * (n + 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ j ∈ Finset.Icc (1 : ℕ) n, j) = ((n * (n + 1)) /. 2)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j)) = (((n ^ (2 : ℕ)) * ((n + 1) ^ (2 : ℕ))) /. (4 * (n ^ (4 : ℕ))))))))
  : Tendsto (fun n : ℝ => (((n ^ (2 : ℕ)) * ((n + 1) ^ (2 : ℕ))) /. (4 * (n ^ (4 : ℕ))))) atTop (𝓝 (1 /. 4)) := by
  sorry

theorem proof_gap_exercise_3901_6
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, (∑ j ∈ Finset.Icc (1 : ℕ) n, (((i /. n) * (j /. n)) * (1 /. (n ^ (2 : ℕ)))))) = (((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, i) = ((n * (n + 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ j ∈ Finset.Icc (1 : ℕ) n, j) = ((n * (n + 1)) /. 2)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((1 /. (n ^ (4 : ℕ))) * (∑ i ∈ Finset.Icc (1 : ℕ) n, i)) * (∑ j ∈ Finset.Icc (1 : ℕ) n, j)) = (((n ^ (2 : ℕ)) * ((n + 1) ^ (2 : ℕ))) /. (4 * (n ^ (4 : ℕ))))))))
  (h5 : Tendsto (fun n : ℝ => (((n ^ (2 : ℕ)) * ((n + 1) ^ (2 : ℕ))) /. (4 * (n ^ (4 : ℕ))))) atTop (𝓝 (1 /. 4)))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in (0 : ℝ)..(1 : ℝ), ((x * y) * (1 : ℝ))) * (1 : ℝ))) = (1 /. 4) := by
  sorry
