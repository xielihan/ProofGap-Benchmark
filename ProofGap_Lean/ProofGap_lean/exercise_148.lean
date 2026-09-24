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

-- exercise: exercise_148

theorem proof_gap_exercise_148_1
  (x : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : m ∈ (Set.univ : Set ℕ))
  (h4 : (x (1 : ℕ)) = a)
  (h5 : (x (2 : ℕ)) = b)
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((x n) = (((x (n - 1)) + (x (n - 2))) /. 2)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (n - 1)) - (x n)) /. 2)))) := by
  sorry

theorem proof_gap_exercise_148_2
  (x : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : m ∈ (Set.univ : Set ℕ))
  (h4 : (x (1 : ℕ)) = a)
  (h5 : (x (2 : ℕ)) = b)
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((x n) = (((x (n - 1)) + (x (n - 2))) /. 2)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (n - 1)) - (x n)) /. 2)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (2 : ℕ)) - (x (1 : ℕ))) /. ((-(2 : ℤ)) ^ (n - 1)))))) := by
  sorry

theorem proof_gap_exercise_148_3
  (x : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : m ∈ (Set.univ : Set ℕ))
  (h4 : (x (1 : ℕ)) = a)
  (h5 : (x (2 : ℕ)) = b)
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((x n) = (((x (n - 1)) + (x (n - 2))) /. 2)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (n - 1)) - (x n)) /. 2)))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (2 : ℕ)) - (x (1 : ℕ))) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = ((b - a) /. ((-(2 : ℤ)) ^ (n - 1)))))) := by
  sorry

theorem proof_gap_exercise_148_4
  (x : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : m ∈ (Set.univ : Set ℕ))
  (h4 : (x (1 : ℕ)) = a)
  (h5 : (x (2 : ℕ)) = b)
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((x n) = (((x (n - 1)) + (x (n - 2))) /. 2)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (n - 1)) - (x n)) /. 2)))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (2 : ℕ)) - (x (1 : ℕ))) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = ((b - a) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((∑ m_1 ∈ Finset.Icc (1 : ℕ) n, ((x (m_1 + 1)) - (x m_1))) + (x (1 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_148_5
  (x : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : m ∈ (Set.univ : Set ℕ))
  (h4 : (x (1 : ℕ)) = a)
  (h5 : (x (2 : ℕ)) = b)
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((x n) = (((x (n - 1)) + (x (n - 2))) /. 2)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (n - 1)) - (x n)) /. 2)))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (2 : ℕ)) - (x (1 : ℕ))) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = ((b - a) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((∑ m_1 ∈ Finset.Icc (1 : ℕ) n, ((x (m_1 + 1)) - (x m_1))) + (x (1 : ℕ)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = (((b - a) * (∑ m_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. ((-(2 : ℤ)) ^ (m_1 - 1))))) + a)))) := by
  sorry

theorem proof_gap_exercise_148_6
  (x : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : m ∈ (Set.univ : Set ℕ))
  (h4 : (x (1 : ℕ)) = a)
  (h5 : (x (2 : ℕ)) = b)
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((x n) = (((x (n - 1)) + (x (n - 2))) /. 2)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (n - 1)) - (x n)) /. 2)))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (2 : ℕ)) - (x (1 : ℕ))) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = ((b - a) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((∑ m_1 ∈ Finset.Icc (1 : ℕ) n, ((x (m_1 + 1)) - (x m_1))) + (x (1 : ℕ)))))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = (((b - a) * (∑ m_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. ((-(2 : ℤ)) ^ (m_1 - 1))))) + a)))))
  : Tendsto (fun n : ℕ => (((b - a) * (∑ m_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. ((-(2 : ℤ)) ^ (m_1 - 1))))) + a)) atTop (𝓝 (((b - a) /. (1 - (-(1 /. 2)))) + a)) := by
  sorry

theorem proof_gap_exercise_148_7
  (x : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : m ∈ (Set.univ : Set ℕ))
  (h4 : (x (1 : ℕ)) = a)
  (h5 : (x (2 : ℕ)) = b)
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((x n) = (((x (n - 1)) + (x (n - 2))) /. 2)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (n - 1)) - (x n)) /. 2)))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (2 : ℕ)) - (x (1 : ℕ))) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = ((b - a) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((∑ m_1 ∈ Finset.Icc (1 : ℕ) n, ((x (m_1 + 1)) - (x m_1))) + (x (1 : ℕ)))))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = (((b - a) * (∑ m_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. ((-(2 : ℤ)) ^ (m_1 - 1))))) + a)))))
  (h12 : Tendsto (fun n : ℕ => (((b - a) * (∑ m_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. ((-(2 : ℤ)) ^ (m_1 - 1))))) + a)) atTop (𝓝 (((b - a) /. (1 - (-(1 /. 2)))) + a)))
  : (((b - a) /. (1 - (-(1 /. 2)))) + a) = ((a + (2 * b)) /. 3) := by
  sorry

theorem proof_gap_exercise_148_8
  (x : (ℕ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (m : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : m ∈ (Set.univ : Set ℕ))
  (h4 : (x (1 : ℕ)) = a)
  (h5 : (x (2 : ℕ)) = b)
  (h6 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((x n) = (((x (n - 1)) + (x (n - 2))) /. 2)))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (n - 1)) - (x n)) /. 2)))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = (((x (2 : ℕ)) - (x (1 : ℕ))) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((x (n + 1)) - (x n)) = ((b - a) /. ((-(2 : ℤ)) ^ (n - 1)))))))
  (h10 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = ((∑ m_1 ∈ Finset.Icc (1 : ℕ) n, ((x (m_1 + 1)) - (x m_1))) + (x (1 : ℕ)))))))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x (n + 1)) = (((b - a) * (∑ m_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. ((-(2 : ℤ)) ^ (m_1 - 1))))) + a)))))
  (h12 : Tendsto (fun n : ℕ => (((b - a) * (∑ m_1 ∈ Finset.Icc (1 : ℕ) n, (1 /. ((-(2 : ℤ)) ^ (m_1 - 1))))) + a)) atTop (𝓝 (((b - a) /. (1 - (-(1 /. 2)))) + a)))
  (h13 : (((b - a) /. (1 - (-(1 /. 2)))) + a) = ((a + (2 * b)) /. 3))
  : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 ((a + (2 * b)) /. 3)) := by
  sorry
