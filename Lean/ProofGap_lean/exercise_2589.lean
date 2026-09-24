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

-- exercise: exercise_2589

theorem proof_gap_exercise_2589_1
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((n ^ (n - 1)) /. (Real.rpow (((2 * (n ^ (2 : ℕ))) + n) + 1) ((n + 1) /. 2)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (n ^ (2 : ℕ)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (a n)) ∧ ((a n) < ((n ^ (n - 1)) /. (Real.rpow ((n : ℝ) ^ (2 : ℕ)) ((n + 1) /. 2))))) ∧ (((n ^ (n - 1)) /. (Real.rpow ((n : ℝ) ^ (2 : ℕ)) ((n + 1) /. 2))) = (b n))))) := by
  sorry

theorem proof_gap_exercise_2589_2
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((n ^ (n - 1)) /. (Real.rpow (((2 * (n ^ (2 : ℕ))) + n) + 1) ((n + 1) /. 2)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (n ^ (2 : ℕ)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (a n)) ∧ ((a n) < ((n ^ (n - 1)) /. (Real.rpow ((n : ℝ) ^ (2 : ℕ)) ((n + 1) /. 2))))) ∧ (((n ^ (n - 1)) /. (Real.rpow ((n : ℝ) ^ (2 : ℕ)) ((n + 1) /. 2))) = (b n))))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0) := by
  sorry

theorem proof_gap_exercise_2589_3
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((n ^ (n - 1)) /. (Real.rpow (((2 * (n ^ (2 : ℕ))) + n) + 1) ((n + 1) /. 2)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (n ^ (2 : ℕ)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (a n)) ∧ ((a n) < ((n ^ (n - 1)) /. (Real.rpow ((n : ℝ) ^ (2 : ℕ)) ((n + 1) /. 2))))) ∧ (((n ^ (n - 1)) /. (Real.rpow ((n : ℝ) ^ (2 : ℕ)) ((n + 1) /. 2))) = (b n))))))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2589_4
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((n ^ (n - 1)) /. (Real.rpow (((2 * (n ^ (2 : ℕ))) + n) + 1) ((n + 1) /. 2)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (n ^ (2 : ℕ)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (a n)) ∧ ((a n) < ((n ^ (n - 1)) /. (Real.rpow ((n : ℝ) ^ (2 : ℕ)) ((n + 1) /. 2))))) ∧ (((n ^ (n - 1)) /. (Real.rpow ((n : ℝ) ^ (2 : ℕ)) ((n + 1) /. 2))) = (b n))))))
  (h4 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))
  (h5 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry
