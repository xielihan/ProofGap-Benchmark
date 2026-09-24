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

-- exercise: exercise_3719

theorem proof_gap_exercise_3719_1
  (F : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : DifferentiableOn ℝ f (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∫ y in (0 : ℝ)..x, (((x + y) * (f y)) * (1 : ℝ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (((2 * x) * (f x)) + (∫ y in (0 : ℝ)..x, ((f y) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3719_2
  (F : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : DifferentiableOn ℝ f (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∫ y in (0 : ℝ)..x, (((x + y) * (f y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (((2 * x) * (f x)) + (∫ y in (0 : ℝ)..x, ((f y) * (1 : ℝ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => F t) x) = (((2 * (f x)) + ((2 * x) * (iteratedDeriv 1 (fun t => f t) x))) + (f x))))) := by
  sorry

theorem proof_gap_exercise_3719_3
  (F : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : DifferentiableOn ℝ f (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∫ y in (0 : ℝ)..x, (((x + y) * (f y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (((2 * x) * (f x)) + (∫ y in (0 : ℝ)..x, ((f y) * (1 : ℝ))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => F t) x) = (((2 * (f x)) + ((2 * x) * (iteratedDeriv 1 (fun t => f t) x))) + (f x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * (f x)) + ((2 * x) * (iteratedDeriv 1 (fun t => f t) x))) + (f x)) = ((3 * (f x)) + ((2 * x) * (iteratedDeriv 1 (fun t => f t) x)))))) := by
  sorry

theorem proof_gap_exercise_3719_4
  (F : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (h1 : DifferentiableOn ℝ f (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = (∫ y in (0 : ℝ)..x, (((x + y) * (f y)) * (1 : ℝ)))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) x) = (((2 * x) * (f x)) + (∫ y in (0 : ℝ)..x, ((f y) * (1 : ℝ))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => F t) x) = (((2 * (f x)) + ((2 * x) * (iteratedDeriv 1 (fun t => f t) x))) + (f x))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * (f x)) + ((2 * x) * (iteratedDeriv 1 (fun t => f t) x))) + (f x)) = ((3 * (f x)) + ((2 * x) * (iteratedDeriv 1 (fun t => f t) x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => F t) x) = ((3 * (f x)) + ((2 * x) * (iteratedDeriv 1 (fun t => f t) x)))))) := by
  sorry
