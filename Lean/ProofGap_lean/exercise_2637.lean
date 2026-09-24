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

-- exercise: exercise_2637

theorem proof_gap_exercise_2637_1
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.log ((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.cos (Real.pi /. n)) ≠ 0) ∧ (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) > 0)))) := by
  sorry

theorem proof_gap_exercise_2637_2
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.log ((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.cos (Real.pi /. n)) ≠ 0) ∧ (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) > 0)))))
  : Tendsto (fun n : ℕ => (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) - 1)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2637_3
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.log ((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.cos (Real.pi /. n)) ≠ 0) ∧ (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) > 0)))))
  (h3 : Tendsto (fun n : ℕ => (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) - 1)) atTop (𝓝 0))
  : Tendsto (fun x : ℝ => (((Real.cosh (Real.pi * x)) - (Real.cos (Real.pi * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (Real.pi ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2637_4
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.log ((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.cos (Real.pi /. n)) ≠ 0) ∧ (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) > 0)))))
  (h3 : Tendsto (fun n : ℕ => (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) - 1)) atTop (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => (((Real.cosh (Real.pi * x)) - (Real.cos (Real.pi * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (Real.pi ^ (2 : ℕ))))
  : Tendsto (fun n : ℕ => ((a n) /. (1 /. (n ^ (2 : ℕ))))) atTop (𝓝 (Real.pi ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2637_5
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.log ((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.cos (Real.pi /. n)) ≠ 0) ∧ (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) > 0)))))
  (h3 : Tendsto (fun n : ℕ => (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) - 1)) atTop (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => (((Real.cosh (Real.pi * x)) - (Real.cos (Real.pi * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (Real.pi ^ (2 : ℕ))))
  (h5 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (n ^ (2 : ℕ))))) atTop (𝓝 (Real.pi ^ (2 : ℕ))))
  : (exists (k : ℝ), (((k ∈ (Set.univ : Set ℝ)) ∧ (k > 0)) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (k * (1 /. (n ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_2637_6
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.log ((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.cos (Real.pi /. n)) ≠ 0) ∧ (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) > 0)))))
  (h3 : Tendsto (fun n : ℕ => (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) - 1)) atTop (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => (((Real.cosh (Real.pi * x)) - (Real.cos (Real.pi * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (Real.pi ^ (2 : ℕ))))
  (h5 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (n ^ (2 : ℕ))))) atTop (𝓝 (Real.pi ^ (2 : ℕ))))
  (h6 : (exists (k : ℝ), (((k ∈ (Set.univ : Set ℝ)) ∧ (k > 0)) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (k * (1 /. (n ^ (2 : ℕ))))))))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (n ^ (2 : ℕ))) else 0) := by
  sorry

theorem proof_gap_exercise_2637_7
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.log ((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.cos (Real.pi /. n)) ≠ 0) ∧ (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) > 0)))))
  (h3 : Tendsto (fun n : ℕ => (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) - 1)) atTop (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => (((Real.cosh (Real.pi * x)) - (Real.cos (Real.pi * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (Real.pi ^ (2 : ℕ))))
  (h5 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (n ^ (2 : ℕ))))) atTop (𝓝 (Real.pi ^ (2 : ℕ))))
  (h6 : (exists (k : ℝ), (((k ∈ (Set.univ : Set ℝ)) ∧ (k > 0)) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (k * (1 /. (n ^ (2 : ℕ))))))))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (n ^ (2 : ℕ))) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2637_8
  (a : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (Real.log ((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.cos (Real.pi /. n)) ≠ 0) ∧ (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) > 0)))))
  (h3 : Tendsto (fun n : ℕ => (((Real.cosh (Real.pi /. n)) /. (Real.cos (Real.pi /. n))) - 1)) atTop (𝓝 0))
  (h4 : Tendsto (fun x : ℝ => (((Real.cosh (Real.pi * x)) - (Real.cos (Real.pi * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (Real.pi ^ (2 : ℕ))))
  (h5 : Tendsto (fun n : ℕ => ((a n) /. (1 /. (n ^ (2 : ℕ))))) atTop (𝓝 (Real.pi ^ (2 : ℕ))))
  (h6 : (exists (k : ℝ), (((k ∈ (Set.univ : Set ℝ)) ∧ (k > 0)) ∧ (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((a n))| ≤ (k * (1 /. (n ^ (2 : ℕ))))))))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (n ^ (2 : ℕ))) else 0))
  (h8 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry
