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

-- exercise: exercise_3127

theorem proof_gap_exercise_3127_1
  (B_1 : (ℝ -> ℝ))
  (B_2 : (ℝ -> ℝ))
  (B_3 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((B_1 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, ((((k /. n) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))) := by
  sorry

theorem proof_gap_exercise_3127_2
  (B_1 : (ℝ -> ℝ))
  (B_2 : (ℝ -> ℝ))
  (B_3 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((B_1 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, ((((k /. n) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((B_1 x) = (x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1)))))) ∧ ((x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1))))) = x)))) := by
  sorry

theorem proof_gap_exercise_3127_3
  (B_1 : (ℝ -> ℝ))
  (B_2 : (ℝ -> ℝ))
  (B_3 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((B_1 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, ((((k /. n) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((B_1 x) = (x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1)))))) ∧ ((x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1))))) = x)))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → ((B_2 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (((((k ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))) := by
  sorry

theorem proof_gap_exercise_3127_4
  (B_1 : (ℝ -> ℝ))
  (B_2 : (ℝ -> ℝ))
  (B_3 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((B_1 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, ((((k /. n) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((B_1 x) = (x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1)))))) ∧ ((x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1))))) = x)))))
  (h5 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → ((B_2 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (((((k ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → (((B_2 x) = (x - ((((n - 1) /. n) * x) * (1 - x)))) ∧ ((x - ((((n - 1) /. n) * x) * (1 - x))) = ((x ^ (2 : ℕ)) + ((x * (1 - x)) /. n)))))) := by
  sorry

theorem proof_gap_exercise_3127_5
  (B_1 : (ℝ -> ℝ))
  (B_2 : (ℝ -> ℝ))
  (B_3 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((B_1 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, ((((k /. n) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((B_1 x) = (x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1)))))) ∧ ((x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1))))) = x)))))
  (h5 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → ((B_2 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (((((k ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h6 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → (((B_2 x) = (x - ((((n - 1) /. n) * x) * (1 - x)))) ∧ ((x - ((((n - 1) /. n) * x) * (1 - x))) = ((x ^ (2 : ℕ)) + ((x * (1 - x)) /. n)))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 3)) → ((B_3 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (((((k ^ (3 : ℕ)) /. (n ^ (3 : ℕ))) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))) := by
  sorry

theorem proof_gap_exercise_3127_6
  (B_1 : (ℝ -> ℝ))
  (B_2 : (ℝ -> ℝ))
  (B_3 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((B_1 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, ((((k /. n) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((B_1 x) = (x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1)))))) ∧ ((x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1))))) = x)))))
  (h5 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → ((B_2 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (((((k ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h6 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → (((B_2 x) = (x - ((((n - 1) /. n) * x) * (1 - x)))) ∧ ((x - ((((n - 1) /. n) * x) * (1 - x))) = ((x ^ (2 : ℕ)) + ((x * (1 - x)) /. n)))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 3)) → ((B_3 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (((((k ^ (3 : ℕ)) /. (n ^ (3 : ℕ))) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 3)) → ((B_3 x) = ((B_2 x) - ((((((n - 1) * (n - 2)) /. (n ^ (2 : ℕ))) * x) * (1 - x)) * ((x /. (n - 2)) + 1)))))) := by
  sorry

theorem proof_gap_exercise_3127_7
  (B_1 : (ℝ -> ℝ))
  (B_2 : (ℝ -> ℝ))
  (B_3 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((B_1 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, ((((k /. n) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → (((B_1 x) = (x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1)))))) ∧ ((x * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (((Nat.choose (n - 1) k) * (x ^ k)) * ((1 - x) ^ ((n - k) - 1))))) = x)))))
  (h5 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → ((B_2 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (((((k ^ (2 : ℕ)) /. (n ^ (2 : ℕ))) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h6 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 2)) → (((B_2 x) = (x - ((((n - 1) /. n) * x) * (1 - x)))) ∧ ((x - ((((n - 1) /. n) * x) * (1 - x))) = ((x ^ (2 : ℕ)) + ((x * (1 - x)) /. n)))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 3)) → ((B_3 x) = (∑ k ∈ Finset.Icc (0 : ℕ) n, (((((k ^ (3 : ℕ)) /. (n ^ (3 : ℕ))) * (Nat.choose n k)) * (x ^ k)) * ((1 - x) ^ (n - k))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 3)) → ((B_3 x) = ((B_2 x) - ((((((n - 1) * (n - 2)) /. (n ^ (2 : ℕ))) * x) * (1 - x)) * ((x /. (n - 2)) + 1)))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) ∧ (n ≥ 3)) → ((B_3 x) = (((((1 - (1 /. n)) * (1 - (2 /. n))) * (x ^ (3 : ℕ))) + (((3 /. n) * (1 - (1 /. n))) * (x ^ (2 : ℕ)))) + ((1 /. (n ^ (2 : ℕ))) * x))))) := by
  sorry
