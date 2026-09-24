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

-- exercise: exercise_2690

theorem proof_gap_exercise_2690_1
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ))))))))
  : Antitone a := by
  sorry

theorem proof_gap_exercise_2690_2
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ))))))))
  (h3 : Antitone a)
  : Tendsto (fun n : ℕ => (a n)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2690_3
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ))))))))
  (h3 : Antitone a)
  (h4 : Tendsto (fun n : ℕ => (a n)) atTop (𝓝 0))
  : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (((|((∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))| = |((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))|) ∧ (|((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))| = |(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))|)) ∧ (|(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))| ≤ 1)))) := by
  sorry

theorem proof_gap_exercise_2690_4
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ))))))))
  (h3 : Antitone a)
  (h4 : Tendsto (fun n : ℕ => (a n)) atTop (𝓝 0))
  (h5 : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (((|((∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))| = |((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))|) ∧ (|((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))| = |(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))|)) ∧ (|(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))| ≤ 1)))))
  : Bornology.IsBounded (Set.range (fun (N : ℕ) => (∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))) := by
  sorry

theorem proof_gap_exercise_2690_5
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ))))))))
  (h3 : Antitone a)
  (h4 : Tendsto (fun n : ℕ => (a n)) atTop (𝓝 0))
  (h5 : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (((|((∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))| = |((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))|) ∧ (|((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))| = |(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))|)) ∧ (|(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))| ≤ 1)))))
  (h6 : Bornology.IsBounded (Set.range (fun (N : ℕ) => (∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) * (b n)) else 0) := by
  sorry

theorem proof_gap_exercise_2690_6
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ))))))))
  (h3 : Antitone a)
  (h4 : Tendsto (fun n : ℕ => (a n)) atTop (𝓝 0))
  (h5 : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (((|((∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))| = |((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))|) ∧ (|((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))| = |(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))|)) ∧ (|(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))| ≤ 1)))))
  (h6 : Bornology.IsBounded (Set.range (fun (N : ℕ) => (∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) * (b n)) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ)))) /. n) else 0) := by
  sorry

theorem proof_gap_exercise_2690_7
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (1 /. n)))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ))))))))
  (h3 : Antitone a)
  (h4 : Tendsto (fun n : ℕ => (a n)) atTop (𝓝 0))
  (h5 : (forall (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) → (((|((∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))| = |((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))|) ∧ (|((∑ n ∈ Finset.Icc (1 : ℕ) N, ((1 /. 2) * ((Real.cos (n * (n - 1))) - (Real.cos (n * (n + 1)))))))| = |(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))|)) ∧ (|(((1 /. 2) * ((Real.cos (0 : ℝ)) - (Real.cos (N * (N + 1))))))| ≤ 1)))))
  (h6 : Bornology.IsBounded (Set.range (fun (N : ℕ) => (∑ n ∈ Finset.Icc (1 : ℕ) N, (b n)))))
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) * (b n)) else 0))
  (h8 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ)))) /. n) else 0))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.sin (n : ℝ)) * (Real.sin ((n : ℝ) ^ (2 : ℕ)))) /. n) else 0) := by
  sorry
