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

-- exercise: exercise_741_2

theorem proof_gap_exercise_741_2_1
  (h1 : x_0 = 0)
  (h2 : f = (fun (x : ℝ) => (if (x ≥ 0) then 1 else (if (x < 0) then (-(1 : ℝ)) else (-(1 : ℝ))))))
  (h3 : g = (fun (x : ℝ) => (if (x ≥ 0) then (-(1 : ℝ)) else (if (x < 0) then 1 else 1))))
  : Not (ContinuousAt f 0) := by
  sorry

theorem proof_gap_exercise_741_2_2
  (h1 : x_0 = 0)
  (h2 : f = (fun (x : ℝ) => (if (x ≥ 0) then 1 else (if (x < 0) then (-(1 : ℝ)) else (-(1 : ℝ))))))
  (h3 : g = (fun (x : ℝ) => (if (x ≥ 0) then (-(1 : ℝ)) else (if (x < 0) then 1 else 1))))
  (h4 : Not (ContinuousAt f 0))
  : Not (ContinuousAt g 0) := by
  sorry

theorem proof_gap_exercise_741_2_3
  (h1 : x_0 = 0)
  (h2 : f = (fun (x : ℝ) => (if (x ≥ 0) then 1 else (if (x < 0) then (-(1 : ℝ)) else (-(1 : ℝ))))))
  (h3 : g = (fun (x : ℝ) => (if (x ≥ 0) then (-(1 : ℝ)) else (if (x < 0) then 1 else 1))))
  (h4 : Not (ContinuousAt f 0))
  (h5 : Not (ContinuousAt g 0))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f x) + (g x)) = 0))) := by
  sorry

theorem proof_gap_exercise_741_2_4
  (h1 : x_0 = 0)
  (h2 : f = (fun (x : ℝ) => (if (x ≥ 0) then 1 else (if (x < 0) then (-(1 : ℝ)) else (-(1 : ℝ))))))
  (h3 : g = (fun (x : ℝ) => (if (x ≥ 0) then (-(1 : ℝ)) else (if (x < 0) then 1 else 1))))
  (h4 : Not (ContinuousAt f 0))
  (h5 : Not (ContinuousAt g 0))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f x) + (g x)) = 0))))
  : Continuous (f + g) := by
  sorry

theorem proof_gap_exercise_741_2_5
  (h1 : x_0 = 0)
  (h2 : f = (fun (x : ℝ) => (if (x ≥ 0) then 1 else (if (x < 0) then (-(1 : ℝ)) else (-(1 : ℝ))))))
  (h3 : g = (fun (x : ℝ) => (if (x ≥ 0) then (-(1 : ℝ)) else (if (x < 0) then 1 else 1))))
  (h4 : Not (ContinuousAt f 0))
  (h5 : Not (ContinuousAt g 0))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((f x) + (g x)) = 0))))
  (h7 : Continuous (f + g))
  : Not (forall (f : (ℝ -> ℝ)) (g : (ℝ -> ℝ)) (x_0 : ℝ), ((((True ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (Not (ContinuousAt f x_0))) ∧ (Not (ContinuousAt g x_0))) → (Not (ContinuousAt (f + g) x_0)))) := by
  sorry
