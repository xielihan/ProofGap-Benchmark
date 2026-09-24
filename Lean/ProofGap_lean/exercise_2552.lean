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

-- exercise: exercise_2552

theorem proof_gap_exercise_2552_1
  (S : (ℕ -> ℝ))
  (h1 : (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i_1 ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (i_1 + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (i_1 + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (i_1 : ℝ) (((2 : ℝ))⁻¹))))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (k + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (k + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (k : ℝ) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_2552_2
  (S : (ℕ -> ℝ))
  (h1 : (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i_1 ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (i_1 + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (i_1 + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (i_1 : ℝ) (((2 : ℝ))⁻¹))))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (k + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (k + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (k : ℝ) (((2 : ℝ))⁻¹))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (((1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) + (Real.rpow (n + 2) (((2 : ℝ))⁻¹))) - (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_2552_3
  (S : (ℕ -> ℝ))
  (h1 : (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i_1 ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (i_1 + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (i_1 + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (i_1 : ℝ) (((2 : ℝ))⁻¹))))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (k + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (k + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (k : ℝ) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (((1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) + (Real.rpow (n + 2) (((2 : ℝ))⁻¹))) - (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) + (1 /. ((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) + (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_2552_4
  (S : (ℕ -> ℝ))
  (h1 : (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i_1 ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (i_1 + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (i_1 + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (i_1 : ℝ) (((2 : ℝ))⁻¹))))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (k + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (k + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (k : ℝ) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (((1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) + (Real.rpow (n + 2) (((2 : ℝ))⁻¹))) - (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) + (1 /. ((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) + (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))))
  : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_2552_5
  (S : (ℕ -> ℝ))
  (h1 : (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ i_1 ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (i_1 + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (i_1 + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (i_1 : ℝ) (((2 : ℝ))⁻¹))))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (∑ k ∈ Finset.Icc (1 : ℕ) n, (((Real.rpow (k + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (k + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (k : ℝ) (((2 : ℝ))⁻¹))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = (((1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) + (Real.rpow (n + 2) (((2 : ℝ))⁻¹))) - (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S n) = ((1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) + (1 /. ((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) + (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))))))))
  (h5 : Tendsto (fun n : ℕ => (S n)) atTop (𝓝 (1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  : (∑' n, if (1 : ℕ) ≤ n then (((Real.rpow (n + 2) (((2 : ℝ))⁻¹)) - (2 * (Real.rpow (n + 1) (((2 : ℝ))⁻¹)))) + (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))) else 0) = (1 - (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) := by
  sorry
