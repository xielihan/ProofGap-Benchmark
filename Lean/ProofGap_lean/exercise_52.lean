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

-- exercise: exercise_52

theorem proof_gap_exercise_52_1
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))) := by
  sorry

theorem proof_gap_exercise_52_2
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((-(k /. (2 * k))) = (-(1 /. 2))))))) := by
  sorry

theorem proof_gap_exercise_52_3
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((-(k /. (2 * k))) = (-(1 /. 2))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(1 /. 2))))))) := by
  sorry

theorem proof_gap_exercise_52_4
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((-(k /. (2 * k))) = (-(1 /. 2))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(1 /. 2))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = ((2 * k) + 1))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = ((k + 1) /. ((2 * k) + 1))))))) := by
  sorry

theorem proof_gap_exercise_52_5
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((-(k /. (2 * k))) = (-(1 /. 2))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(1 /. 2))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = ((2 * k) + 1))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = ((k + 1) /. ((2 * k) + 1))))))))
  : Tendsto (fun k : ℕ => (-(1 /. 2))) atTop (𝓝 (-(1 /. 2))) := by
  sorry

theorem proof_gap_exercise_52_6
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((-(k /. (2 * k))) = (-(1 /. 2))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(1 /. 2))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = ((2 * k) + 1))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = ((k + 1) /. ((2 * k) + 1))))))))
  (h5 : Tendsto (fun k : ℕ => (-(1 /. 2))) atTop (𝓝 (-(1 /. 2))))
  : Tendsto (fun k : ℕ => ((k + 1) /. ((2 * k) + 1))) atTop (𝓝 (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_52_7
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((-(k /. (2 * k))) = (-(1 /. 2))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(1 /. 2))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = ((2 * k) + 1))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = ((k + 1) /. ((2 * k) + 1))))))))
  (h5 : Tendsto (fun k : ℕ => (-(1 /. 2))) atTop (𝓝 (-(1 /. 2))))
  (h6 : Tendsto (fun k : ℕ => ((k + 1) /. ((2 * k) + 1))) atTop (𝓝 (1 /. 2)))
  : (-(1 /. 2)) ≠ (1 /. 2) := by
  sorry

theorem proof_gap_exercise_52_8
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((-(k /. (2 * k))) = (-(1 /. 2))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(1 /. 2))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = ((2 * k) + 1))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = ((k + 1) /. ((2 * k) + 1))))))))
  (h5 : Tendsto (fun k : ℕ => (-(1 /. 2))) atTop (𝓝 (-(1 /. 2))))
  (h6 : Tendsto (fun k : ℕ => ((k + 1) /. ((2 * k) + 1))) atTop (𝓝 (1 /. 2)))
  (h7 : (-(1 /. 2)) ≠ (1 /. 2))
  : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun n : ℕ => (∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n))) atTop (𝓝 L)))) := by
  sorry

theorem proof_gap_exercise_52_9
  (h1 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(k /. (2 * k)))))))))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((-(k /. (2 * k))) = (-(1 /. 2))))))))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = (2 * k))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = (-(1 /. 2))))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), ((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n = ((2 * k) + 1))) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n)) = ((k + 1) /. ((2 * k) + 1))))))))
  (h5 : Tendsto (fun k : ℕ => (-(1 /. 2))) atTop (𝓝 (-(1 /. 2))))
  (h6 : Tendsto (fun k : ℕ => ((k + 1) /. ((2 * k) + 1))) atTop (𝓝 (1 /. 2)))
  (h7 : (-(1 /. 2)) ≠ (1 /. 2))
  (h8 : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun n : ℕ => (∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n))) atTop (𝓝 L)))))
  : Not (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun n : ℕ => (∑ i ∈ Finset.Icc (1 : ℕ) n, ((((-(1 : ℤ)) ^ (i - 1)) * i) /. n))) atTop (𝓝 L)))) := by
  sorry
