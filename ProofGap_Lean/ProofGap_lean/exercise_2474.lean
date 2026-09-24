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

-- exercise: exercise_2474

theorem proof_gap_exercise_2474_1
  (y : (ℝ -> ℝ))
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : V_x ∈ (Set.univ : Set ℝ))
  (h2 : V_y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ Real.pi)) → ((y x) = (Real.sin x)))))
  (h4 : V_x = ((Real.pi ^ (2 : ℕ)) /. 2))
  : V_x = (Real.pi * (∫ x in (0 : ℝ)..Real.pi, (((Real.sin x) ^ (2 : ℕ)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2474_2
  (y : (ℝ -> ℝ))
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : V_x ∈ (Set.univ : Set ℝ))
  (h2 : V_y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ Real.pi)) → ((y x) = (Real.sin x)))))
  (h4 : V_x = (Real.pi * (∫ x in (0 : ℝ)..Real.pi, (((Real.sin x) ^ (2 : ℕ)) * (1 : ℝ)))))
  : V_x = ((Real.pi ^ (2 : ℕ)) /. 2) := by
  sorry

theorem proof_gap_exercise_2474_3
  (y : (ℝ -> ℝ))
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : V_x ∈ (Set.univ : Set ℝ))
  (h2 : V_y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ Real.pi)) → ((y x) = (Real.sin x)))))
  (h4 : V_x = (Real.pi * (∫ x in (0 : ℝ)..Real.pi, (((Real.sin x) ^ (2 : ℕ)) * (1 : ℝ)))))
  (h5 : V_x = ((Real.pi ^ (2 : ℕ)) /. 2))
  (h6 : V_y = (2 * (Real.pi ^ (2 : ℕ))))
  : V_y = ((2 * Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((x * (Real.sin x)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2474_4
  (y : (ℝ -> ℝ))
  (V_x : ℝ)
  (V_y : ℝ)
  (h1 : V_x ∈ (Set.univ : Set ℝ))
  (h2 : V_y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ Real.pi)) → ((y x) = (Real.sin x)))))
  (h4 : V_x = (Real.pi * (∫ x in (0 : ℝ)..Real.pi, (((Real.sin x) ^ (2 : ℕ)) * (1 : ℝ)))))
  (h5 : V_x = ((Real.pi ^ (2 : ℕ)) /. 2))
  (h6 : V_y = ((2 * Real.pi) * (∫ x in (0 : ℝ)..Real.pi, ((x * (Real.sin x)) * (1 : ℝ)))))
  : V_y = (2 * (Real.pi ^ (2 : ℕ))) := by
  sorry
