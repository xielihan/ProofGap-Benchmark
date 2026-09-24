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

-- exercise: exercise_1421

theorem proof_gap_exercise_1421_1
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = |(x)|))))
  : (y (0 : ℝ)) = 0 := by
  sorry

theorem proof_gap_exercise_1421_2
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = |(x)|))))
  (h2 : (y (0 : ℝ)) = 0)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((y x) = |(x)|) ∧ (|(x)| > 0)))) := by
  sorry

theorem proof_gap_exercise_1421_3
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = |(x)|))))
  (h2 : (y (0 : ℝ)) = 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((y x) = |(x)|) ∧ (|(x)| > 0)))))
  : Not (DifferentiableAt ℝ y 0) := by
  sorry

theorem proof_gap_exercise_1421_4
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = |(x)|))))
  (h2 : (y (0 : ℝ)) = 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((y x) = |(x)|) ∧ (|(x)| > 0)))))
  (h4 : Not (DifferentiableAt ℝ y 0))
  : (lpMinimumPoints y) = ({x | x = 0}) := by
  sorry

theorem proof_gap_exercise_1421_5
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = |(x)|))))
  (h2 : (y (0 : ℝ)) = 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((y x) = |(x)|) ∧ (|(x)| > 0)))))
  (h4 : Not (DifferentiableAt ℝ y 0))
  (h5 : (lpMinimumPoints y) = ({x | x = 0}))
  : (y (0 : ℝ)) = 0 := by
  sorry

theorem proof_gap_exercise_1421_6
  (y : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = |(x)|))))
  (h2 : (y (0 : ℝ)) = 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((y x) = |(x)|) ∧ (|(x)| > 0)))))
  (h4 : Not (DifferentiableAt ℝ y 0))
  (h5 : (lpMinimumPoints y) = ({x | x = 0}))
  (h6 : (y (0 : ℝ)) = 0)
  : (lpMaximumPoints y) = ∅ := by
  sorry
