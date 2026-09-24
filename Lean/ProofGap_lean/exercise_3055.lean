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

-- exercise: exercise_3055

theorem proof_gap_exercise_3055_1
  (h1 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))) := by
  sorry

theorem proof_gap_exercise_3055_2
  (h1 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = ((Real.sin (Real.pi /. 2)) /. (((2 : ℕ) ^ n) * (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))))))) := by
  sorry

theorem proof_gap_exercise_3055_3
  (h1 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = ((Real.sin (Real.pi /. 2)) /. (((2 : ℕ) ^ n) * (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (((Real.pi /. ((2 : ℕ) ^ (n + 1))) /. (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))) * (2 /. Real.pi))))) := by
  sorry

theorem proof_gap_exercise_3055_4
  (h1 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = ((Real.sin (Real.pi /. 2)) /. (((2 : ℕ) ^ n) * (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (((Real.pi /. ((2 : ℕ) ^ (n + 1))) /. (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))) * (2 /. Real.pi))))))
  : Tendsto (fun x : ℝ => (x /. (Real.sin x))) (𝓝[≠] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_3055_5
  (h1 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = ((Real.sin (Real.pi /. 2)) /. (((2 : ℕ) ^ n) * (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (((Real.pi /. ((2 : ℕ) ^ (n + 1))) /. (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))) * (2 /. Real.pi))))))
  (h5 : Tendsto (fun x : ℝ => (x /. (Real.sin x))) (𝓝[≠] 0) (𝓝 1))
  : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (2 /. Real.pi)) := by
  sorry

theorem proof_gap_exercise_3055_6
  (h1 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = ((Real.sin (Real.pi /. 2)) /. (((2 : ℕ) ^ n) * (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (((Real.pi /. ((2 : ℕ) ^ (n + 1))) /. (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))) * (2 /. Real.pi))))))
  (h5 : Tendsto (fun x : ℝ => (x /. (Real.sin x))) (𝓝[≠] 0) (𝓝 1))
  (h6 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (2 /. Real.pi)))
  : (∏' n, if (1 : ℕ) ≤ n then (Real.cos (Real.pi /. ((2 : ℕ) ^ (n + 1)))) else 1) = (2 /. Real.pi) := by
  sorry

theorem proof_gap_exercise_3055_7
  (h1 : P = (fun (n : ℕ) => (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (∏ i ∈ Finset.Icc (1 : ℕ) n, (Real.cos (Real.pi /. ((2 : ℕ) ^ (i + 1)))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = ((Real.sin (Real.pi /. 2)) /. (((2 : ℕ) ^ n) * (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((P n) = (((Real.pi /. ((2 : ℕ) ^ (n + 1))) /. (Real.sin (Real.pi /. ((2 : ℕ) ^ (n + 1))))) * (2 /. Real.pi))))))
  (h5 : Tendsto (fun x : ℝ => (x /. (Real.sin x))) (𝓝[≠] 0) (𝓝 1))
  (h6 : Tendsto (fun n : ℕ => (P n)) atTop (𝓝 (2 /. Real.pi)))
  (h7 : (∏' n, if (1 : ℕ) ≤ n then (Real.cos (Real.pi /. ((2 : ℕ) ^ (n + 1)))) else 1) = (2 /. Real.pi))
  : (∏' n, if (1 : ℕ) ≤ n then (Real.cos (Real.pi /. ((2 : ℕ) ^ (n + 1)))) else 1) = (2 /. Real.pi) := by
  sorry
