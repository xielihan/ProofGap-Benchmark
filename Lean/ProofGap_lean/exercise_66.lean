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

-- exercise: exercise_66

theorem proof_gap_exercise_66_1
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! ≥ ((1 /. 2) * (Real.rpow (n : ℝ) (n /. 2)))))) := by
  sorry

theorem proof_gap_exercise_66_2
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! ≥ ((1 /. 2) * (Real.rpow (n : ℝ) (n /. 2)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) ≤ ((Real.rpow (2 : ℝ) (1 /. n)) * (1 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_66_3
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! ≥ ((1 /. 2) * (Real.rpow (n : ℝ) (n /. 2)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) ≤ ((Real.rpow (2 : ℝ) (1 /. n)) * (1 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  : Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (1 /. n)) * (1 /. (Real.rpow n (((2 : ℝ))⁻¹))))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_66_4
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! ≥ ((1 /. 2) * (Real.rpow (n : ℝ) (n /. 2)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) ≤ ((Real.rpow (2 : ℝ) (1 /. n)) * (1 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  (h3 : Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (1 /. n)) * (1 /. (Real.rpow n (((2 : ℝ))⁻¹))))) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_66_5
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! ≥ ((1 /. 2) * (Real.rpow (n : ℝ) (n /. 2)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) ≤ ((Real.rpow (2 : ℝ) (1 /. n)) * (1 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))))))))
  (h3 : Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (1 /. n)) * (1 /. (Real.rpow n (((2 : ℝ))⁻¹))))) atTop (𝓝 0))
  (h4 : Tendsto (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))) atTop (𝓝 0) := by
  sorry
