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

-- exercise: exercise_79

theorem proof_gap_exercise_79_1
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))) := by
  sorry

theorem proof_gap_exercise_79_2
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))) := by
  sorry

theorem proof_gap_exercise_79_3
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) < (x n)))) := by
  sorry

theorem proof_gap_exercise_79_4
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((x (n + 1)) < (x n)))))
  (h7 : (x (0 : ℕ)) ≥ (x (1 : ℕ)))
  : Antitone x := by
  sorry

theorem proof_gap_exercise_79_5
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) < (x n)))))
  (h7 : Antitone x)
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (x n)))) := by
  sorry

theorem proof_gap_exercise_79_6
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) < (x n)))))
  (h7 : Antitone x)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (x n)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) < 1))) := by
  sorry

theorem proof_gap_exercise_79_7
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) < (x n)))))
  (h7 : Antitone x)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (x n)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) < 1))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < 1))) := by
  sorry

theorem proof_gap_exercise_79_8
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) < (x n)))))
  (h7 : Antitone x)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (x n)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) < 1))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < 1))))
  : Bornology.IsBounded (Set.range x) := by
  sorry

theorem proof_gap_exercise_79_9
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) < (x n)))))
  (h7 : Antitone x)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (x n)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) < 1))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < 1))))
  (h11 : Bornology.IsBounded (Set.range x))
  : (∃ l, Filter.Tendsto x Filter.atTop (𝓝 l)) := by
  sorry

theorem proof_gap_exercise_79_10
  (x : (ℕ -> ℝ))
  (k : ℕ)
  (h1 : True)
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (∏ k_1 ∈ Finset.Icc (1 : ℕ) n, (1 - (1 /. ((2 : ℕ) ^ k_1))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x n) * (1 - (1 /. ((2 : ℕ) ^ (n + 1))))) < (x n)))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) < (x n)))))
  (h7 : Antitone x)
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < (x n)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) < 1))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < 1))))
  (h11 : Bornology.IsBounded (Set.range x))
  (h12 : (∃ l, Filter.Tendsto x Filter.atTop (𝓝 l)))
  : (∃ l, Filter.Tendsto x Filter.atTop (𝓝 l)) := by
  sorry
