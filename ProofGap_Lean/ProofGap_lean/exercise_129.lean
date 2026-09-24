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

-- exercise: exercise_129

theorem proof_gap_exercise_129_1
  (x : (ℕ -> ℝ))
  (y : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : True)
  (h2 : True)
  (h3 : True)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 /. n)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((y n) = n))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = ((x n) * (y n))))))
  : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_129_2
  (x : (ℕ -> ℝ))
  (y : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : True)
  (h2 : True)
  (h3 : True)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 /. n)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((y n) = n))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = ((x n) * (y n))))))
  (h7 : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = 1))) := by
  sorry

theorem proof_gap_exercise_129_3
  (x : (ℕ -> ℝ))
  (y : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : True)
  (h2 : True)
  (h3 : True)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 /. n)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((y n) = n))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = ((x n) * (y n))))))
  (h7 : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = 1))))
  : Tendsto (fun n : ℕ => (p n)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_129_4
  (x : (ℕ -> ℝ))
  (y : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : True)
  (h2 : True)
  (h3 : True)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 /. n)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((y n) = n))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = ((x n) * (y n))))))
  (h7 : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = 1))))
  (h9 : Tendsto (fun n : ℕ => (p n)) atTop (𝓝 1))
  : Not (Tendsto (fun n : ℕ => (p n)) atTop (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_129_5
  (x : (ℕ -> ℝ))
  (y : (ℕ -> ℝ))
  (p : (ℕ -> ℝ))
  (h1 : True)
  (h2 : True)
  (h3 : True)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (1 /. n)))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((y n) = n))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = ((x n) * (y n))))))
  (h7 : Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = 1))))
  (h9 : Tendsto (fun n : ℕ => (p n)) atTop (𝓝 1))
  (h10 : Not (Tendsto (fun n : ℕ => (p n)) atTop (𝓝 0)))
  : ((Tendsto (fun n : ℕ => (x n)) atTop (𝓝 0)) ∧ (Tendsto (fun n : ℕ => (p n)) atTop (𝓝 1))) ∧ (Not (Tendsto (fun n : ℕ => (p n)) atTop (𝓝 0))) := by
  sorry
