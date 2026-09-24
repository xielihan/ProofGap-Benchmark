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

-- exercise: exercise_1283

theorem proof_gap_exercise_1283_1
  (h1 : f = (fun (x : ℝ) => (x + (Real.sin x))))
  : MonotoneOn f (Set.Ioi 0) := by
  sorry

theorem proof_gap_exercise_1283_2
  (h1 : f = (fun (x : ℝ) => (x + (Real.sin x))))
  (h2 : MonotoneOn f (Set.Ioi 0))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 + (Real.cos x))))) := by
  sorry

theorem proof_gap_exercise_1283_3
  (h1 : f = (fun (x : ℝ) => (x + (Real.sin x))))
  (h2 : MonotoneOn f (Set.Ioi 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 + (Real.cos x))))))
  : (iteratedDeriv 1 (fun t => f t) (Real.pi /. 2)) = 1 := by
  sorry

theorem proof_gap_exercise_1283_4
  (h1 : f = (fun (x : ℝ) => (x + (Real.sin x))))
  (h2 : MonotoneOn f (Set.Ioi 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 + (Real.cos x))))))
  (h4 : (iteratedDeriv 1 (fun t => f t) (Real.pi /. 2)) = 1)
  : (iteratedDeriv 1 (fun t => f t) Real.pi) = 0 := by
  sorry

theorem proof_gap_exercise_1283_5
  (h1 : f = (fun (x : ℝ) => (x + (Real.sin x))))
  (h2 : MonotoneOn f (Set.Ioi 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 + (Real.cos x))))))
  (h4 : (iteratedDeriv 1 (fun t => f t) (Real.pi /. 2)) = 1)
  (h5 : (iteratedDeriv 1 (fun t => f t) Real.pi) = 0)
  : (iteratedDeriv 1 (fun t => f t) ((3 * Real.pi) /. 2)) = 1 := by
  sorry

theorem proof_gap_exercise_1283_6
  (h1 : f = (fun (x : ℝ) => (x + (Real.sin x))))
  (h2 : MonotoneOn f (Set.Ioi 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 + (Real.cos x))))))
  (h4 : (iteratedDeriv 1 (fun t => f t) (Real.pi /. 2)) = 1)
  (h5 : (iteratedDeriv 1 (fun t => f t) Real.pi) = 0)
  (h6 : (iteratedDeriv 1 (fun t => f t) ((3 * Real.pi) /. 2)) = 1)
  : Not (MonotoneOn (fun (x1) => (iteratedDeriv 1 (fun t => f t) x1)) (Set.Ioi 0)) := by
  sorry

theorem proof_gap_exercise_1283_7
  (h1 : f = (fun (x : ℝ) => (x + (Real.sin x))))
  (h2 : MonotoneOn f (Set.Ioi 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 + (Real.cos x))))))
  (h4 : (iteratedDeriv 1 (fun t => f t) (Real.pi /. 2)) = 1)
  (h5 : (iteratedDeriv 1 (fun t => f t) Real.pi) = 0)
  (h6 : (iteratedDeriv 1 (fun t => f t) ((3 * Real.pi) /. 2)) = 1)
  (h7 : Not (MonotoneOn (fun (x1) => (iteratedDeriv 1 (fun t => f t) x1)) (Set.Ioi 0)))
  : Not (AntitoneOn (fun (x1) => (iteratedDeriv 1 (fun t => f t) x1)) (Set.Ioi 0)) := by
  sorry

theorem proof_gap_exercise_1283_8
  (h1 : f = (fun (x : ℝ) => (x + (Real.sin x))))
  (h2 : MonotoneOn f (Set.Ioi 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioi 0))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 + (Real.cos x))))))
  (h4 : (iteratedDeriv 1 (fun t => f t) (Real.pi /. 2)) = 1)
  (h5 : (iteratedDeriv 1 (fun t => f t) Real.pi) = 0)
  (h6 : (iteratedDeriv 1 (fun t => f t) ((3 * Real.pi) /. 2)) = 1)
  (h7 : Not (MonotoneOn (fun (x1) => (iteratedDeriv 1 (fun t => f t) x1)) (Set.Ioi 0)))
  (h8 : Not (AntitoneOn (fun (x1) => (iteratedDeriv 1 (fun t => f t) x1)) (Set.Ioi 0)))
  : Not (forall (f : (ℝ -> ℝ)), ((MonotoneOn f (Set.Ioi 0)) → ((MonotoneOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) (Set.Ioi 0)) ∨ (AntitoneOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) (Set.Ioi 0))))) := by
  sorry
