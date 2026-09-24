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

-- exercise: exercise_2672

theorem proof_gap_exercise_2672_1
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))) := by
  sorry

theorem proof_gap_exercise_2672_2
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))) := by
  sorry

theorem proof_gap_exercise_2672_3
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  : (∀ n_1, 0 < b n_1) := by
  sorry

theorem proof_gap_exercise_2672_4
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  (h4 : (∀ n_1, 0 < b n_1))
  : Antitone b := by
  sorry

theorem proof_gap_exercise_2672_5
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  (h4 : (∀ n_1, 0 < b n_1))
  (h5 : Antitone b)
  : Tendsto (fun k : ℕ => (b k)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2672_6
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  (h4 : (∀ n_1, 0 < b n_1))
  (h5 : Antitone b)
  (h6 : Tendsto (fun k : ℕ => (b k)) atTop (𝓝 0))
  : Summable (fun (k : ℕ) => if (1 : ℕ) ≤ k then (((-(1 : ℤ)) ^ k) * (b k)) else 0) := by
  sorry

theorem proof_gap_exercise_2672_7
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  (h4 : (∀ n_1, 0 < b n_1))
  (h5 : Antitone b)
  (h6 : Tendsto (fun k : ℕ => (b k)) atTop (𝓝 0))
  (h7 : Summable (fun (k : ℕ) => if (1 : ℕ) ≤ k then (((-(1 : ℤ)) ^ k) * (b k)) else 0))
  : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (exists (K : ℕ), ((((K ∈ (Set.univ : Set ℕ)) ∧ (K ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ k ∈ Finset.Icc (1 : ℕ) K, (((-(1 : ℤ)) ^ k) * (b k))) ≤ (∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)))) ∧ ((∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) ≤ (∑ k ∈ Finset.Icc (1 : ℕ) (K + 1), (((-(1 : ℤ)) ^ k) * (b k)))))))) := by
  sorry

theorem proof_gap_exercise_2672_8
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  (h4 : (∀ n_1, 0 < b n_1))
  (h5 : Antitone b)
  (h6 : Tendsto (fun k : ℕ => (b k)) atTop (𝓝 0))
  (h7 : Summable (fun (k : ℕ) => if (1 : ℕ) ≤ k then (((-(1 : ℤ)) ^ k) * (b k)) else 0))
  (h8 : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (exists (K : ℕ), ((((K ∈ (Set.univ : Set ℕ)) ∧ (K ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ k ∈ Finset.Icc (1 : ℕ) K, (((-(1 : ℤ)) ^ k) * (b k))) ≤ (∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)))) ∧ ((∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) ≤ (∑ k ∈ Finset.Icc (1 : ℕ) (K + 1), (((-(1 : ℤ)) ^ k) * (b k)))))))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n) else 0) := by
  sorry

theorem proof_gap_exercise_2672_9
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  (h4 : (∀ n_1, 0 < b n_1))
  (h5 : Antitone b)
  (h6 : Tendsto (fun k : ℕ => (b k)) atTop (𝓝 0))
  (h7 : Summable (fun (k : ℕ) => if (1 : ℕ) ≤ k then (((-(1 : ℤ)) ^ k) * (b k)) else 0))
  (h8 : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (exists (K : ℕ), ((((K ∈ (Set.univ : Set ℕ)) ∧ (K ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ k ∈ Finset.Icc (1 : ℕ) K, (((-(1 : ℤ)) ^ k) * (b k))) ≤ (∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)))) ∧ ((∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) ≤ (∑ k ∈ Finset.Icc (1 : ℕ) (K + 1), (((-(1 : ℤ)) ^ k) * (b k)))))))))
  (h9 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n) else 0))
  : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n))| else 0) := by
  sorry

theorem proof_gap_exercise_2672_10
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  (h4 : (∀ n_1, 0 < b n_1))
  (h5 : Antitone b)
  (h6 : Tendsto (fun k : ℕ => (b k)) atTop (𝓝 0))
  (h7 : Summable (fun (k : ℕ) => if (1 : ℕ) ≤ k then (((-(1 : ℤ)) ^ k) * (b k)) else 0))
  (h8 : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (exists (K : ℕ), ((((K ∈ (Set.univ : Set ℕ)) ∧ (K ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ k ∈ Finset.Icc (1 : ℕ) K, (((-(1 : ℤ)) ^ k) * (b k))) ≤ (∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)))) ∧ ((∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) ≤ (∑ k ∈ Finset.Icc (1 : ℕ) (K + 1), (((-(1 : ℤ)) ^ k) * (b k)))))))))
  (h9 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n) else 0))
  (h10 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n))| else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n))‖ else 0) := by
  sorry

theorem proof_gap_exercise_2672_11
  (b : (ℕ -> ℝ))
  (h1 : b = (fun (k : ℕ) => (∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (1 /. n))))
  (h2 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ n ∈ Finset.Icc (k ^ (2 : ℕ)) (((k + 1) ^ (2 : ℕ)) - 1), (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) = (((-(1 : ℤ)) ^ k) * (b k))))))
  (h3 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (((2 /. (k + 1)) < (b k)) ∧ ((b k) < (2 /. k))))))
  (h4 : (∀ n_1, 0 < b n_1))
  (h5 : Antitone b)
  (h6 : Tendsto (fun k : ℕ => (b k)) atTop (𝓝 0))
  (h7 : Summable (fun (k : ℕ) => if (1 : ℕ) ≤ k then (((-(1 : ℤ)) ^ k) * (b k)) else 0))
  (h8 : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (exists (K : ℕ), ((((K ∈ (Set.univ : Set ℕ)) ∧ (K ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ k ∈ Finset.Icc (1 : ℕ) K, (((-(1 : ℤ)) ^ k) * (b k))) ≤ (∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)))) ∧ ((∑ n ∈ Finset.Icc (1 : ℕ) N, (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n)) ≤ (∑ k ∈ Finset.Icc (1 : ℕ) (K + 1), (((-(1 : ℤ)) ^ k) * (b k)))))))))
  (h9 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n) else 0))
  (h10 : ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n))| else 0))
  (h11 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n))‖ else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((((-(1 : ℝ)) ^ ⌊(Real.rpow (n : ℝ) (((2 : ℝ))⁻¹))⌋) /. n))‖ else 0) := by
  sorry
