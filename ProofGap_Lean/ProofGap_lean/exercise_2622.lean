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

-- exercise: exercise_2622

theorem proof_gap_exercise_2622_1
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))) := by
  sorry

theorem proof_gap_exercise_2622_2
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) < ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k)))))))) := by
  sorry

theorem proof_gap_exercise_2622_3
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) < ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k)))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) > ((1 /. 2) * ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k))))))))) := by
  sorry

theorem proof_gap_exercise_2622_4
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) < ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) > ((1 /. 2) * ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k))))))))))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (BddAbove (Set.range S)) := by
  sorry

theorem proof_gap_exercise_2622_5
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) < ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) > ((1 /. 2) * ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k))))))))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (BddAbove (Set.range S)))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2622_6
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) < ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) > ((1 /. 2) * ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k))))))))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (BddAbove (Set.range S)))
  (h7 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  : (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Not (BddAbove (Set.range S))) := by
  sorry

theorem proof_gap_exercise_2622_7
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) < ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) > ((1 /. 2) * ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k))))))))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (BddAbove (Set.range S)))
  (h7 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h8 : (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Not (BddAbove (Set.range S))))
  : (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2622_8
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) < ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) > ((1 /. 2) * ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k))))))))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (BddAbove (Set.range S)))
  (h7 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h8 : (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Not (BddAbove (Set.range S))))
  (h9 : (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) := by
  sorry

theorem proof_gap_exercise_2622_9
  (a : (ℕ -> ℝ))
  (h1 : (∀ n_1, 0 < a n_1) ∧ (StrictAnti a))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≥ 1))) → (((S : ℕ → _) k) = (∑ i ∈ Finset.Icc (1 : ℕ) k, (a i)))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (S ((2 : ℕ) ^ n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) < ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((S ((2 : ℕ) ^ n)) > ((1 /. 2) * ((a (1 : ℕ)) + (∑ k ∈ Finset.Icc (1 : ℕ) n, (((2 : ℕ) ^ k) * (a ((2 : ℕ) ^ k))))))))))
  (h6 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (BddAbove (Set.range S)))
  (h7 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h8 : (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (Not (BddAbove (Set.range S))))
  (h9 : (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h10 : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)))
  : (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((2 : ℕ) ^ n) * (a ((2 : ℕ) ^ n))) else 0)) := by
  sorry
