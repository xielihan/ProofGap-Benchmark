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

-- exercise: exercise_2567_2

theorem proof_gap_exercise_2567_2_1
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : True)
  (h3 : True)
  (h4 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((a n_1) ≥ 0) ∧ ((b n_1) ≥ 0)))))
  (h5 : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h6 : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (b n_1) else 0))
  : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((max (a n_1) (b n_1)) ≥ (a n_1)) ∧ ((a n_1) ≥ 0)))) := by
  sorry

theorem proof_gap_exercise_2567_2_2
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : True)
  (h3 : True)
  (h4 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((a n_1) ≥ 0) ∧ ((b n_1) ≥ 0)))))
  (h5 : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h6 : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (b n_1) else 0))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((max (a n_1) (b n_1)) ≥ (a n_1)) ∧ ((a n_1) ≥ 0)))))
  : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (max (a n_1) (b n_1)) else 0) := by
  sorry

theorem proof_gap_exercise_2567_2_3
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : True)
  (h3 : True)
  (h4 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((a n_1) ≥ 0) ∧ ((b n_1) ≥ 0)))))
  (h5 : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h6 : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (b n_1) else 0))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((max (a n_1) (b n_1)) ≥ (a n_1)) ∧ ((a n_1) ≥ 0)))))
  (h8 : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (max (a n_1) (b n_1)) else 0))
  : ¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (max (a n_1) (b n_1)) else 0) := by
  sorry
