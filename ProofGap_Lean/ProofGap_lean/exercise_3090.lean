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

-- exercise: exercise_3090

theorem proof_gap_exercise_3090_1
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_3090_2
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))) := by
  sorry

theorem proof_gap_exercise_3090_3
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)) := by
  sorry

theorem proof_gap_exercise_3090_4
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))) := by
  sorry

theorem proof_gap_exercise_3090_5
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))) := by
  sorry

theorem proof_gap_exercise_3090_6
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))) := by
  sorry

theorem proof_gap_exercise_3090_7
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  (h8 : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  : ((1 /. 2) < p) → ((p ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))) := by
  sorry

theorem proof_gap_exercise_3090_8
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  (h8 : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h9 : ((1 /. 2) < p) → ((p ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  : ((1 /. 2) < p) → ((p ≤ 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))) := by
  sorry

theorem proof_gap_exercise_3090_9
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  (h8 : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h9 : ((1 /. 2) < p) → ((p ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h10 : ((1 /. 2) < p) → ((p ≤ 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  : (0 < p) → ((p ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))) := by
  sorry

theorem proof_gap_exercise_3090_10
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  (h8 : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h9 : ((1 /. 2) < p) → ((p ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h10 : ((1 /. 2) < p) → ((p ≤ 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  (h11 : (0 < p) → ((p ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  : (0 < p) → ((p ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))) := by
  sorry

theorem proof_gap_exercise_3090_11
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  (h8 : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h9 : ((1 /. 2) < p) → ((p ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h10 : ((1 /. 2) < p) → ((p ≤ 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  (h11 : (0 < p) → ((p ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h12 : (0 < p) → ((p ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  : (0 < p) → ((p ≤ (1 /. 2)) → (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))) := by
  sorry

theorem proof_gap_exercise_3090_12
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  (h8 : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h9 : ((1 /. 2) < p) → ((p ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h10 : ((1 /. 2) < p) → ((p ≤ 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  (h11 : (0 < p) → ((p ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h12 : (0 < p) → ((p ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h13 : (0 < p) → ((p ≤ (1 /. 2)) → (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  : (p ≤ 0) → (Not (Tendsto (fun n : ℕ => ((Real.rpow (-(1 : ℝ)) (n - 1)) /. (Real.rpow n p))) atTop (𝓝 0))) := by
  sorry

theorem proof_gap_exercise_3090_13
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  (h8 : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h9 : ((1 /. 2) < p) → ((p ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h10 : ((1 /. 2) < p) → ((p ≤ 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  (h11 : (0 < p) → ((p ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h12 : (0 < p) → ((p ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h13 : (0 < p) → ((p ≤ (1 /. 2)) → (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  (h14 : (p ≤ 0) → (Not (Tendsto (fun n : ℕ => ((Real.rpow (-(1 : ℝ)) (n - 1)) /. (Real.rpow n p))) atTop (𝓝 0))))
  : (p ≤ 0) → (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)) := by
  sorry

theorem proof_gap_exercise_3090_14
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P N) = (∏ n_1 ∈ Finset.Icc (1 : ℕ) N, (1 + (((-(1 : ℤ)) ^ (n_1 - 1)) /. (Real.rpow (n_1 : ℝ) p))))))))))
  (h3 : (p > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0)))
  (h4 : (p > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0))))
  (h5 : (p > 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  (h6 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)))‖ else 0))))
  (h7 : ((1 /. 2) < p) → ((p ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0))))
  (h8 : ((1 /. 2) < p) → ((p ≤ 1) → ((∑' n, if (1 : ℕ) ≤ n then ((((-(1 : ℤ)) ^ (n + 1)) /. (Real.rpow (n : ℝ) p)) ^ (2 : ℕ)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h9 : ((1 /. 2) < p) → ((p ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h10 : ((1 /. 2) < p) → ((p ≤ 1) → (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  (h11 : (0 < p) → ((p ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (2 * p))) else 0))))
  (h12 : (0 < p) → ((p ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 + (((-(1 : ℤ)) ^ (n - 1)) /. (Real.rpow (n : ℝ) p))) ≠ 0)))))
  (h13 : (0 < p) → ((p ≤ (1 /. 2)) → (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l))))
  (h14 : (p ≤ 0) → (Not (Tendsto (fun n : ℕ => ((Real.rpow (-(1 : ℝ)) (n - 1)) /. (Real.rpow n p))) atTop (𝓝 0))))
  (h15 : (p ≤ 0) → (¬ ∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)))
  : (p ∈ ({p_1 | (p_1 ∈ (Set.univ : Set ℝ)) ∧ (p_1 > (1 /. 2))})) ↔ (∃ l, Filter.Tendsto P Filter.atTop (𝓝 l)) := by
  sorry
