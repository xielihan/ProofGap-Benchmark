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

-- exercise: exercise_2585

theorem proof_gap_exercise_2585_1
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * k_1) + 1))⁻¹))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ≠ 0))) := by
  sorry

theorem proof_gap_exercise_2585_2
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * k_1) + 1))⁻¹))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ≠ 0))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_2585_3
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * k_1) + 1))⁻¹))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))))))
  (h4 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)) := by
  sorry

theorem proof_gap_exercise_2585_4
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * k_1) + 1))⁻¹))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)) := by
  sorry

theorem proof_gap_exercise_2585_5
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * k_1) + 1))⁻¹))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)))
  (h5 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 L))
  : ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) < 1 := by
  sorry

theorem proof_gap_exercise_2585_6
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * k_1) + 1))⁻¹))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)))
  (h5 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)))
  (h6 : ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) < 1)
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2585_7
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ) (k : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * k_1) + 1))⁻¹))))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ≠ 0))))
  (h3 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)))
  (h5 : Tendsto (fun n : ℕ => ((a (n + 1)) /. (a n))) atTop (𝓝 ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1)))
  (h6 : ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - 1) < 1)
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) - (Real.rpow (2 : ℝ) ((((2 * n) + 3))⁻¹)))) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry
