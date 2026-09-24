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

-- exercise: exercise_58

theorem proof_gap_exercise_58_1
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))) := by
  sorry

theorem proof_gap_exercise_58_2
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((1 + 1) ^ n) > ((n * (n - 1)) /. 2)))) := by
  sorry

theorem proof_gap_exercise_58_3
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((1 + 1) ^ n) > ((n * (n - 1)) /. 2)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) > ((n * (n - 1)) /. 2)))) := by
  sorry

theorem proof_gap_exercise_58_4
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((1 + 1) ^ n) > ((n * (n - 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) > ((n * (n - 1)) /. 2)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (n /. ((2 : ℕ) ^ n))))) := by
  sorry

theorem proof_gap_exercise_58_5
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((1 + 1) ^ n) > ((n * (n - 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) > ((n * (n - 1)) /. 2)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (n /. ((2 : ℕ) ^ n))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → ((n /. ((2 : ℕ) ^ n)) < (2 /. (n - 1))))) := by
  sorry

theorem proof_gap_exercise_58_6
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((1 + 1) ^ n) > ((n * (n - 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) > ((n * (n - 1)) /. 2)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (n /. ((2 : ℕ) ^ n))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → ((n /. ((2 : ℕ) ^ n)) < (2 /. (n - 1))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (2 /. (n - 1))))) := by
  sorry

theorem proof_gap_exercise_58_7
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((1 + 1) ^ n) > ((n * (n - 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) > ((n * (n - 1)) /. 2)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (n /. ((2 : ℕ) ^ n))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → ((n /. ((2 : ℕ) ^ n)) < (2 /. (n - 1))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (2 /. (n - 1))))))
  : Tendsto (fun n : ℕ => (2 /. (n - 1))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_58_8
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((1 + 1) ^ n) > ((n * (n - 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) > ((n * (n - 1)) /. 2)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (n /. ((2 : ℕ) ^ n))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → ((n /. ((2 : ℕ) ^ n)) < (2 /. (n - 1))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (2 /. (n - 1))))))
  (h7 : Tendsto (fun n : ℕ => (2 /. (n - 1))) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => (n /. (Real.rpow (2 : ℝ) n))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_58_9
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) = ((1 + 1) ^ n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((1 + 1) ^ n) > ((n * (n - 1)) /. 2)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (((2 : ℕ) ^ n) > ((n * (n - 1)) /. 2)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (n /. ((2 : ℕ) ^ n))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → ((n /. ((2 : ℕ) ^ n)) < (2 /. (n - 1))))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 2)) → (0 < (2 /. (n - 1))))))
  (h7 : Tendsto (fun n : ℕ => (2 /. (n - 1))) atTop (𝓝 0))
  (h8 : Tendsto (fun n : ℕ => (n /. (Real.rpow (2 : ℝ) n))) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => (n /. (Real.rpow (2 : ℝ) n))) atTop (𝓝 0) := by
  sorry
