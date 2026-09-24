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

-- exercise: exercise_41

theorem proof_gap_exercise_41_1
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (n /. (n + 1))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| = (1 /. (n + 1))))) := by
  sorry

theorem proof_gap_exercise_41_2
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (n /. (n + 1))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| = (1 /. (n + 1))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ ((1 /. (n + 1)) < v_uCE_uB5)) → (|(((x n) - 1))| < v_uCE_uB5))))) := by
  sorry

theorem proof_gap_exercise_41_3
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (n /. (n + 1))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| = (1 /. (n + 1))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ ((1 /. (n + 1)) < v_uCE_uB5)) → (|(((x n) - 1))| < v_uCE_uB5))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → ((1 /. (n + 1)) < v_uCE_uB5))))) := by
  sorry

theorem proof_gap_exercise_41_4
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (n /. (n + 1))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| = (1 /. (n + 1))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ ((1 /. (n + 1)) < v_uCE_uB5)) → (|(((x n) - 1))| < v_uCE_uB5))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → ((1 /. (n + 1)) < v_uCE_uB5))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → (|(((x n) - 1))| < v_uCE_uB5))))) := by
  sorry

theorem proof_gap_exercise_41_5
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (n /. (n + 1))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| = (1 /. (n + 1))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ ((1 /. (n + 1)) < v_uCE_uB5)) → (|(((x n) - 1))| < v_uCE_uB5))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → ((1 /. (n + 1)) < v_uCE_uB5))))))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → (|(((x n) - 1))| < v_uCE_uB5))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) ∧ (N = ⌊(1 /. v_uCE_uB5)⌋))))) := by
  sorry

theorem proof_gap_exercise_41_6
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (n /. (n + 1))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| = (1 /. (n + 1))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ ((1 /. (n + 1)) < v_uCE_uB5)) → (|(((x n) - 1))| < v_uCE_uB5))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → ((1 /. (n + 1)) < v_uCE_uB5))))))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → (|(((x n) - 1))| < v_uCE_uB5))))))
  (h7 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) ∧ (N = ⌊(1 /. v_uCE_uB5)⌋))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N = ⌊(1 /. v_uCE_uB5)⌋)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| < v_uCE_uB5))))))) := by
  sorry

theorem proof_gap_exercise_41_7
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (n /. (n + 1))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| = (1 /. (n + 1))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ ((1 /. (n + 1)) < v_uCE_uB5)) → (|(((x n) - 1))| < v_uCE_uB5))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → ((1 /. (n + 1)) < v_uCE_uB5))))))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → (|(((x n) - 1))| < v_uCE_uB5))))))
  (h7 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) ∧ (N = ⌊(1 /. v_uCE_uB5)⌋))))))
  (h8 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N = ⌊(1 /. v_uCE_uB5)⌋)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| < v_uCE_uB5))))))))
  : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_41_8
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (n /. (n + 1))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| = (1 /. (n + 1))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ ((1 /. (n + 1)) < v_uCE_uB5)) → (|(((x n) - 1))| < v_uCE_uB5))))))
  (h5 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → ((1 /. (n + 1)) < v_uCE_uB5))))))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (v_uCE_uB5 : ℝ), ((((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) ∧ (n > ((1 /. v_uCE_uB5) - 1))) → (|(((x n) - 1))| < v_uCE_uB5))))))
  (h7 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ (Set.univ : Set ℕ)) ∧ (N = ⌊(1 /. v_uCE_uB5)⌋))))))
  (h8 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N = ⌊(1 /. v_uCE_uB5)⌋)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n > N)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|(((x n) - 1))| < v_uCE_uB5))))))))
  (h9 : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 1))
  : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 1) := by
  sorry
