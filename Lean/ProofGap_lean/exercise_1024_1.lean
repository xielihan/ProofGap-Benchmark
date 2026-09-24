import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_1024_1

theorem proof_gap_exercise_1024_1_1
  (P : (ℕ × ℝ -> ℝ))
  (PuCC_u85 : (ℕ × ℝ -> ℝ))
  (h1 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (k_1 * (x ^ (k_1 - 1))))))))
  (h2 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((PuCC_u85 (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (x ^ k_1))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((PuCC_u85 (n, x)) = ((x * (1 - (x ^ n))) /. (1 - x))))) := by
  sorry

theorem proof_gap_exercise_1024_1_2
  (P : (ℕ × ℝ -> ℝ))
  (PuCC_u85 : (ℕ × ℝ -> ℝ))
  (h1 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (k_1 * (x ^ (k_1 - 1))))))))
  (h2 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((PuCC_u85 (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (x ^ k_1))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((PuCC_u85 (n, x)) = ((x * (1 - (x ^ n))) /. (1 - x))))))
  : (forall (n : ℕ) (x : ℝ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun n_1 : ℝ => (PuCC_u85 (n, n_1))) t) x) = (P (n, x))))) := by
  sorry

theorem proof_gap_exercise_1024_1_3
  (P : (ℕ × ℝ -> ℝ))
  (PuCC_u85 : (ℕ × ℝ -> ℝ))
  (h1 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (k_1 * (x ^ (k_1 - 1))))))))
  (h2 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((PuCC_u85 (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (x ^ k_1))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((PuCC_u85 (n, x)) = ((x * (1 - (x ^ n))) /. (1 - x))))))
  (h4 : (forall (n : ℕ) (x : ℝ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun n_1 : ℝ => (PuCC_u85 (n, n_1))) t) x) = (P (n, x))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => ((t * (1 - (t ^ n))) /. (1 - t))) x) = (P (n, x))))) := by
  sorry

theorem proof_gap_exercise_1024_1_4
  (P : (ℕ × ℝ -> ℝ))
  (PuCC_u85 : (ℕ × ℝ -> ℝ))
  (h1 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (k_1 * (x ^ (k_1 - 1))))))))
  (h2 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((PuCC_u85 (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (x ^ k_1))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((PuCC_u85 (n, x)) = ((x * (1 - (x ^ n))) /. (1 - x))))))
  (h4 : (forall (n : ℕ) (x : ℝ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun n_1 : ℝ => (PuCC_u85 (n, n_1))) t) x) = (P (n, x))))))
  (h5 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => ((t * (1 - (t ^ n))) /. (1 - t))) x) = (P (n, x))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((P (n, x)) = (((1 - ((n + 1) * (x ^ n))) + (n * (x ^ (n + 1)))) /. ((1 - x) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1024_1_5
  (P : (ℕ × ℝ -> ℝ))
  (PuCC_u85 : (ℕ × ℝ -> ℝ))
  (h1 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (k_1 * (x ^ (k_1 - 1))))))))
  (h2 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((PuCC_u85 (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (x ^ k_1))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((PuCC_u85 (n, x)) = ((x * (1 - (x ^ n))) /. (1 - x))))))
  (h4 : (forall (n : ℕ) (x : ℝ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun n_1 : ℝ => (PuCC_u85 (n, n_1))) t) x) = (P (n, x))))))
  (h5 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => ((t * (1 - (t ^ n))) /. (1 - t))) x) = (P (n, x))))))
  (h6 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((P (n, x)) = (((1 - ((n + 1) * (x ^ n))) + (n * (x ^ (n + 1)))) /. ((1 - x) ^ (2 : ℕ)))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((P (n, x)) = (((1 - ((n + 1) * (x ^ n))) + (n * (x ^ (n + 1)))) /. ((1 - x) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1024_1_6
  (P : (ℕ × ℝ -> ℝ))
  (PuCC_u85 : (ℕ × ℝ -> ℝ))
  (h1 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((P (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (k_1 * (x ^ (k_1 - 1))))))))
  (h2 : (forall (k : ℕ) (n : ℕ) (x : ℝ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((PuCC_u85 (n, x)) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (x ^ k_1))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((PuCC_u85 (n, x)) = ((x * (1 - (x ^ n))) /. (1 - x))))))
  (h4 : (forall (n : ℕ) (x : ℝ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) → ((iteratedDeriv 1 (fun t => (fun n_1 : ℝ => (PuCC_u85 (n, n_1))) t) x) = (P (n, x))))))
  (h5 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((iteratedDeriv 1 (fun t => ((t * (1 - (t ^ n))) /. (1 - t))) x) = (P (n, x))))))
  (h6 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((P (n, x)) = (((1 - ((n + 1) * (x ^ n))) + (n * (x ^ (n + 1)))) /. ((1 - x) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((P (n, x)) = (((1 - ((n + 1) * (x ^ n))) + (n * (x ^ (n + 1)))) /. ((1 - x) ^ (2 : ℕ)))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (x ≠ 1)) → ((P (n, x)) = (((1 - ((n + 1) * (x ^ n))) + (n * (x ^ (n + 1)))) /. ((1 - x) ^ (2 : ℕ)))))) := by
  sorry
