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

-- exercise: exercise_3056

theorem proof_gap_exercise_3056_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))) := by
  sorry

theorem proof_gap_exercise_3056_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = ((Real.sin x) /. (((2 : ℕ) ^ n) * (Real.sin (x /. ((2 : ℕ) ^ n)))))))) := by
  sorry

theorem proof_gap_exercise_3056_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = ((Real.sin x) /. (((2 : ℕ) ^ n) * (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))) * ((Real.sin x) /. x))))) := by
  sorry

theorem proof_gap_exercise_3056_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = ((Real.sin x) /. (((2 : ℕ) ^ n) * (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))) * ((Real.sin x) /. x))))))
  : Tendsto (fun t : ℝ => (t /. (Real.sin t))) (𝓝[≠] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_3056_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = ((Real.sin x) /. (((2 : ℕ) ^ n) * (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))) * ((Real.sin x) /. x))))))
  (h7 : Tendsto (fun t : ℝ => (t /. (Real.sin t))) (𝓝[≠] 0) (𝓝 1))
  : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 ((Real.sin x) /. x)) := by
  sorry

theorem proof_gap_exercise_3056_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = ((Real.sin x) /. (((2 : ℕ) ^ n) * (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))) * ((Real.sin x) /. x))))))
  (h7 : Tendsto (fun t : ℝ => (t /. (Real.sin t))) (𝓝[≠] 0) (𝓝 1))
  (h8 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 ((Real.sin x) /. x)))
  : (∏' n, if (1 : ℕ) ≤ n then (Real.cos (x /. ((2 : ℕ) ^ n))) else 1) = ((Real.sin x) /. x) := by
  sorry

theorem proof_gap_exercise_3056_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (x /. ((2 : ℕ) ^ i))))))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = ((Real.sin x) /. (((2 : ℕ) ^ n) * (Real.sin (x /. ((2 : ℕ) ^ n)))))))))
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Real.sin (x /. ((2 : ℕ) ^ n))) ≠ 0)) → ((P n) = (((x /. ((2 : ℕ) ^ n)) /. (Real.sin (x /. ((2 : ℕ) ^ n)))) * ((Real.sin x) /. x))))))
  (h7 : Tendsto (fun t : ℝ => (t /. (Real.sin t))) (𝓝[≠] 0) (𝓝 1))
  (h8 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 ((Real.sin x) /. x)))
  (h9 : (∏' n, if (1 : ℕ) ≤ n then (Real.cos (x /. ((2 : ℕ) ^ n))) else 1) = ((Real.sin x) /. x))
  : (∏' n, if (1 : ℕ) ≤ n then (Real.cos (x /. ((2 : ℕ) ^ n))) else 1) = ((Real.sin x) /. x) := by
  sorry
