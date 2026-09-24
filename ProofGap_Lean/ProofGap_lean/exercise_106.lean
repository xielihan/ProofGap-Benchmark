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

-- exercise: exercise_106

theorem proof_gap_exercise_106_1
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (((-(1 : ℤ)) ^ n) * n)))))
  : ((sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) : EReal) = ⊥ := by
  sorry

theorem proof_gap_exercise_106_2
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (((-(1 : ℤ)) ^ n) * n)))))
  (h3 : ((sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) : EReal) = ⊥)
  : ((sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) : EReal) = ⊤ := by
  sorry

theorem proof_gap_exercise_106_3
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (((-(1 : ℤ)) ^ n) * n)))))
  (h3 : ((sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) : EReal) = ⊥)
  (h4 : ((sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) : EReal) = ⊤)
  : ((Filter.liminf (fun n : ℕ => ((x n) : EReal)) atTop) : EReal) = ⊥ := by
  sorry

theorem proof_gap_exercise_106_4
  (x : (ℕ -> ℝ))
  (h1 : True)
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((x n) = (((-(1 : ℤ)) ^ n) * n)))))
  (h3 : ((sInf ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) : EReal) = ⊥)
  (h4 : ((sSup ({x_n | (n ∈ ({n_1 : ℕ | 0 < n_1}))})) : EReal) = ⊤)
  (h5 : ((Filter.liminf (fun n : ℕ => ((x n) : EReal)) atTop) : EReal) = ⊥)
  : ((Filter.limsup (fun n : ℕ => ((x n) : EReal)) atTop) : EReal) = ⊤ := by
  sorry
