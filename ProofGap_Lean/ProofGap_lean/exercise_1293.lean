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

-- exercise: exercise_1293

theorem proof_gap_exercise_1293_1
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (k_1 : ℕ), ((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k_1 ≤ n)) → (((a k_1) ∈ (Set.univ : Set ℝ)) ∧ ((b k_1) ∈ (Set.univ : Set ℝ))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) ≥ 0))) := by
  sorry

theorem proof_gap_exercise_1293_2
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (k_1 : ℕ), ((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k_1 ≤ n)) → (((a k_1) ∈ (Set.univ : Set ℝ)) ∧ ((b k_1) ∈ (Set.univ : Set ℝ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) ≥ 0))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) = ((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1293_3
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (k_1 : ℕ), ((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k_1 ≤ n)) → (((a k_1) ∈ (Set.univ : Set ℝ)) ∧ ((b k_1) ∈ (Set.univ : Set ℝ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) ≥ 0))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) = ((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ)))) ≥ 0))) := by
  sorry

theorem proof_gap_exercise_1293_4
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (k_1 : ℕ), ((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k_1 ≤ n)) → (((a k_1) ∈ (Set.univ : Set ℝ)) ∧ ((b k_1) ∈ (Set.univ : Set ℝ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) ≥ 0))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) = ((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ)))) ≥ 0))))
  : ((4 * ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1))) ^ (2 : ℕ))) - ((4 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ)))) * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ))))) ≤ 0 := by
  sorry

theorem proof_gap_exercise_1293_5
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (k_1 : ℕ), ((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k_1 ≤ n)) → (((a k_1) ∈ (Set.univ : Set ℝ)) ∧ ((b k_1) ∈ (Set.univ : Set ℝ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) ≥ 0))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) = ((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ)))) ≥ 0))))
  (h8 : ((4 * ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1))) ^ (2 : ℕ))) - ((4 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ)))) * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ))))) ≤ 0)
  : ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1))) ^ (2 : ℕ)) ≤ ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_1293_6
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : (forall (k_1 : ℕ), ((((k_1 ∈ (Set.univ : Set ℕ)) ∧ (k_1 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k_1 ≤ n)) → (((a k_1) ∈ (Set.univ : Set ℝ)) ∧ ((b k_1) ∈ (Set.univ : Set ℝ))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) ≥ 0))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((((a k_1) * x) + (b k_1)) ^ (2 : ℕ))) = ((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ))))))))
  (h7 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + ((2 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1)))) * x)) + (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ)))) ≥ 0))))
  (h8 : ((4 * ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1))) ^ (2 : ℕ))) - ((4 * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ)))) * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ))))) ≤ 0)
  (h9 : ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1))) ^ (2 : ℕ)) ≤ ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ)))))
  : ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) * (b k_1))) ^ (2 : ℕ)) ≤ ((∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((a k_1) ^ (2 : ℕ))) * (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, ((b k_1) ^ (2 : ℕ)))) := by
  sorry
