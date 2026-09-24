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

-- exercise: exercise_2118

theorem proof_gap_exercise_2118_1
  : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))) := by
  sorry

theorem proof_gap_exercise_2118_2
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.sinh x) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}) := by
  sorry

theorem proof_gap_exercise_2118_3
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.sinh x) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((((Real.cosh x) ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => (Real.cosh t)) x)))))}) := by
  sorry

theorem proof_gap_exercise_2118_4
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.sinh x) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h3 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((((Real.cosh x) ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => (Real.cosh t)) x)))))}))
  : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = ((((Real.cosh x) ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => (Real.cosh t)) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_7 x) = ((((1 /. 3) * ((Real.cosh x) ^ (3 : ℕ))) - (Real.cosh x)) + C))))))}) := by
  sorry

theorem proof_gap_exercise_2118_5
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.sinh x) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h3 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((((Real.cosh x) ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => (Real.cosh t)) x)))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = ((((Real.cosh x) ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => (Real.cosh t)) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_7 x) = ((((1 /. 3) * ((Real.cosh x) ^ (3 : ℕ))) - (Real.cosh x)) + C))))))}))
  : ({F_8 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_8 t) x) = (((Real.sinh x) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_9 x) = ((((1 /. 3) * ((Real.cosh x) ^ (3 : ℕ))) - (Real.cosh x)) + C))))))}) := by
  sorry

theorem proof_gap_exercise_2118_6
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = (((Real.sinh x) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h3 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((((Real.sinh x) ^ (2 : ℕ)) * (Real.sinh x)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((((Real.cosh x) ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => (Real.cosh t)) x)))))}))
  (h4 : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = ((((Real.cosh x) ^ (2 : ℕ)) - 1) * (iteratedDeriv 1 (fun t => (Real.cosh t)) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_7 x) = ((((1 /. 3) * ((Real.cosh x) ^ (3 : ℕ))) - (Real.cosh x)) + C))))))}))
  (h5 : ({F_8 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_8 t) x) = (((Real.sinh x) ^ (3 : ℕ)) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_9 x) = ((((1 /. 3) * ((Real.cosh x) ^ (3 : ℕ))) - (Real.cosh x)) + C))))))}))
  : (exists (C : ℝ), (C ∈ (Set.univ : Set ℝ))) := by
  sorry
