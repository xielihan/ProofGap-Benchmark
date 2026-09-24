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

-- exercise: exercise_4

theorem proof_gap_exercise_4_1
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n = 1)) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))) := by
  sorry

theorem proof_gap_exercise_4_2
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n = 1)) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k))))))) := by
  sorry

theorem proof_gap_exercise_4_3
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n = 1)) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k)) = ((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k))))))) := by
  sorry

theorem proof_gap_exercise_4_4
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n = 1)) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k)) = ((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k)) = (((2 : ℕ) ^ (k + 1)) - 1)))))) := by
  sorry

theorem proof_gap_exercise_4_5
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n = 1)) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k)) = ((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k)) = (((2 : ℕ) ^ (k + 1)) - 1)))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))) := by
  sorry

theorem proof_gap_exercise_4_6
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n = 1)) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k)) = ((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k)) = (((2 : ℕ) ^ (k + 1)) - 1)))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))) := by
  sorry

theorem proof_gap_exercise_4_7
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n = 1)) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) + ((2 : ℕ) ^ k)) = ((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → (((((2 : ℕ) ^ k) - 1) + ((2 : ℕ) ^ k)) = (((2 : ℕ) ^ (k + 1)) - 1)))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) (k - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ k) - 1))) ∧ (n = (k + 1))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), ((2 : ℕ) ^ i)) = (((2 : ℕ) ^ n) - 1)))) := by
  sorry
