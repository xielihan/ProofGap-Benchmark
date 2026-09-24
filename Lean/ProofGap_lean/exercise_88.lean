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

-- exercise: exercise_88

theorem proof_gap_exercise_88_1
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (1 ≤ k)) ∧ (k ≤ n)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1))))))))
  : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| = (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k))))))) := by
  sorry

theorem proof_gap_exercise_88_2
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (1 ≤ k)) ∧ (k ≤ n)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1))))))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| = (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k))))))))
  : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k)) > (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n)))))))) := by
  sorry

theorem proof_gap_exercise_88_3
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (1 ≤ k)) ∧ (k ≤ n)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1))))))))
  (h3 : (forall (m : ℕ), ((m ∈ ({n_1 : ℕ | 0 < n_1})) → (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| = (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k))))))))
  (h4 : (forall (m : ℕ), ((m ∈ ({n_1 : ℕ | 0 < n_1})) → (forall (n : ℕ), ((((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (m = (2 * n))) ∧ (n > 1)) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k)) > (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n)))))))))
  : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n))) = (1 /. 2)))))) := by
  sorry

theorem proof_gap_exercise_88_4
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (1 ≤ k)) ∧ (k ≤ n)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1))))))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| = (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k))))))))
  (h4 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k)) > (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n)))))))))
  (h5 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n))) = (1 /. 2)))))))
  : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| > (1 /. 2)))))) := by
  sorry

theorem proof_gap_exercise_88_5
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (1 ≤ k)) ∧ (k ≤ n)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1))))))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| = (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k))))))))
  (h4 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k)) > (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n)))))))))
  (h5 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n))) = (1 /. 2)))))))
  (h6 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| > (1 /. 2)))))))
  : Not (CauchySeq x) := by
  sorry

theorem proof_gap_exercise_88_6
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (1 ≤ k)) ∧ (k ≤ n)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1))))))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| = (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k))))))))
  (h4 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k)) > (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n)))))))))
  (h5 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n))) = (1 /. 2)))))))
  (h6 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| > (1 /. 2)))))))
  (h7 : Not (CauchySeq x))
  : (¬ ∃ l, Filter.Tendsto x Filter.atTop (𝓝 l)) := by
  sorry

theorem proof_gap_exercise_88_7
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (1 ≤ k)) ∧ (k ≤ n)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∑ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. k_1))))))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| = (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k))))))))
  (h4 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. k)) > (∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n)))))))))
  (h5 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → ((∑ k ∈ Finset.Icc (n + 1) (2 * n), (1 /. (2 * n))) = (1 /. 2)))))))
  (h6 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m = (2 * n))) → (|(((x m) - (x n)))| > (1 /. 2)))))))
  (h7 : Not (CauchySeq x))
  (h8 : (¬ ∃ l, Filter.Tendsto x Filter.atTop (𝓝 l)))
  : (¬ ∃ l, Filter.Tendsto x Filter.atTop (𝓝 l)) := by
  sorry
