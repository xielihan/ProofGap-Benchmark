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

-- exercise: exercise_2312

theorem proof_gap_exercise_2312_1
  : (∫ x in (0 : ℝ)..Real.pi, ((x * (SignType.sign (Real.cos x) : ℝ)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(Real.pi /. 2), (x * (1 : ℝ))) + (∫ x in (Real.pi /. 2)..Real.pi, ((-x) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2312_2
  (h1 : (∫ x in (0 : ℝ)..Real.pi, ((x * (SignType.sign (Real.cos x) : ℝ)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(Real.pi /. 2), (x * (1 : ℝ))) + (∫ x in (Real.pi /. 2)..Real.pi, ((-x) * (1 : ℝ)))))
  : ((∫ x in (0 : ℝ)..(Real.pi /. 2), (x * (1 : ℝ))) + (∫ x in (Real.pi /. 2)..Real.pi, ((-x) * (1 : ℝ)))) = (-((Real.pi ^ (2 : ℕ)) /. 4)) := by
  sorry

theorem proof_gap_exercise_2312_3
  (h1 : (∫ x in (0 : ℝ)..Real.pi, ((x * (SignType.sign (Real.cos x) : ℝ)) * (1 : ℝ))) = ((∫ x in (0 : ℝ)..(Real.pi /. 2), (x * (1 : ℝ))) + (∫ x in (Real.pi /. 2)..Real.pi, ((-x) * (1 : ℝ)))))
  (h2 : ((∫ x in (0 : ℝ)..(Real.pi /. 2), (x * (1 : ℝ))) + (∫ x in (Real.pi /. 2)..Real.pi, ((-x) * (1 : ℝ)))) = (-((Real.pi ^ (2 : ℕ)) /. 4)))
  : (∫ x in (0 : ℝ)..Real.pi, ((x * (SignType.sign (Real.cos x) : ℝ)) * (1 : ℝ))) = (-((Real.pi ^ (2 : ℕ)) /. 4)) := by
  sorry
