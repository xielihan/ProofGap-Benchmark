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

-- exercise: exercise_1028

theorem proof_gap_exercise_1028_1
  (f : (ℝ -> ℝ))
  (T : ℝ)
  (h1 : T ∈ (Set.univ : Set ℝ))
  (h2 : DifferentiableOn ℝ f (Set.univ : Set ℝ))
  (h3 : Function.Periodic f T)
  (h4 : T ≠ 0)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (f x)))) := by
  sorry

theorem proof_gap_exercise_1028_2
  (f : (ℝ -> ℝ))
  (T : ℝ)
  (h1 : T ∈ (Set.univ : Set ℝ))
  (h2 : DifferentiableOn ℝ f (Set.univ : Set ℝ))
  (h3 : Function.Periodic f T)
  (h4 : T ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (f x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f t) (x + T)) = (iteratedDeriv 1 (fun t => f t) x)))) := by
  sorry

theorem proof_gap_exercise_1028_3
  (f : (ℝ -> ℝ))
  (T : ℝ)
  (h1 : T ∈ (Set.univ : Set ℝ))
  (h2 : DifferentiableOn ℝ f (Set.univ : Set ℝ))
  (h3 : Function.Periodic f T)
  (h4 : T ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (f x)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f t) (x + T)) = (iteratedDeriv 1 (fun t => f t) x)))))
  : Function.Periodic (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) T := by
  sorry

theorem proof_gap_exercise_1028_4
  (f : (ℝ -> ℝ))
  (T : ℝ)
  (h1 : T ∈ (Set.univ : Set ℝ))
  (h2 : DifferentiableOn ℝ f (Set.univ : Set ℝ))
  (h3 : Function.Periodic f T)
  (h4 : T ≠ 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (f x)))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => f t) (x + T)) = (iteratedDeriv 1 (fun t => f t) x)))))
  (h7 : Function.Periodic (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) T)
  : Function.Periodic (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => f t) x1)) T := by
  sorry
