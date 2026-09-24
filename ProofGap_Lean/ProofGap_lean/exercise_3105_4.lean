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

-- exercise: exercise_3105_4

theorem proof_gap_exercise_3105_4_1
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ m)) → (Tendsto (fun m_1 : ℕ => (((m_1)! * (m_1 ^ n)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) m_1, (n + k_1)))) atTop (𝓝 (v_uCE_u93 (n : ℝ)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((v_uCE_u93 (x + 1)) = (x * (v_uCE_u93 x))))))
  (h5 : (v_uCE_u93 (1 : ℝ)) = 1)
  : (n = 1) → ((v_uCE_u93 (n : ℝ)) = 1) := by
  sorry

theorem proof_gap_exercise_3105_4_2
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ m)) → (Tendsto (fun m_1 : ℕ => (((m_1)! * (m_1 ^ n)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) m_1, (n + k_1)))) atTop (𝓝 (v_uCE_u93 (n : ℝ)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((v_uCE_u93 (x + 1)) = (x * (v_uCE_u93 x))))))
  (h5 : (v_uCE_u93 (1 : ℝ)) = 1)
  (h6 : (n = 1) → ((v_uCE_u93 (n : ℝ)) = 1))
  : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = ((n - 1) * (v_uCE_u93 (n - 1)))) := by
  sorry

theorem proof_gap_exercise_3105_4_3
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ m)) → (Tendsto (fun m_1 : ℕ => (((m_1)! * (m_1 ^ n)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) m_1, (n + k_1)))) atTop (𝓝 (v_uCE_u93 (n : ℝ)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((v_uCE_u93 (x + 1)) = (x * (v_uCE_u93 x))))))
  (h5 : (v_uCE_u93 (1 : ℝ)) = 1)
  (h6 : (n = 1) → ((v_uCE_u93 (n : ℝ)) = 1))
  (h7 : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = ((n - 1) * (v_uCE_u93 (n - 1)))))
  : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = (((n - 1) * (n - 2)) * (v_uCE_u93 (n - 2)))) := by
  sorry

theorem proof_gap_exercise_3105_4_4
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ m)) → (Tendsto (fun m_1 : ℕ => (((m_1)! * (m_1 ^ n)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) m_1, (n + k_1)))) atTop (𝓝 (v_uCE_u93 (n : ℝ)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((v_uCE_u93 (x + 1)) = (x * (v_uCE_u93 x))))))
  (h5 : (v_uCE_u93 (1 : ℝ)) = 1)
  (h6 : (n = 1) → ((v_uCE_u93 (n : ℝ)) = 1))
  (h7 : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = ((n - 1) * (v_uCE_u93 (n - 1)))))
  (h8 : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = (((n - 1) * (n - 2)) * (v_uCE_u93 (n - 2)))))
  : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = (((n - 1))! * (v_uCE_u93 (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3105_4_5
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (m : ℕ), ((m ∈ (Set.univ : Set ℕ)) → (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ≤ m)) → (Tendsto (fun m_1 : ℕ => (((m_1)! * (m_1 ^ n)) /. (∏ k_1 ∈ Finset.Icc (0 : ℕ) m_1, (n + k_1)))) atTop (𝓝 (v_uCE_u93 (n : ℝ)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 < x_1}))) → ((v_uCE_u93 (x + 1)) = (x * (v_uCE_u93 x))))))
  (h5 : (v_uCE_u93 (1 : ℝ)) = 1)
  (h6 : (n = 1) → ((v_uCE_u93 (n : ℝ)) = 1))
  (h7 : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = ((n - 1) * (v_uCE_u93 (n - 1)))))
  (h8 : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = (((n - 1) * (n - 2)) * (v_uCE_u93 (n - 2)))))
  (h9 : (n ≥ 2) → ((v_uCE_u93 (n : ℝ)) = (((n - 1))! * (v_uCE_u93 (1 : ℝ)))))
  : (v_uCE_u93 (n : ℝ)) = ((n - 1))! := by
  sorry
