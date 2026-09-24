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

-- exercise: exercise_1753

theorem proof_gap_exercise_1753_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) = ((((1 /. 2) * (1 - (Real.cos (6 * x)))) * (1 /. 4)) * ((3 * (Real.sin (2 * x))) - (Real.sin (6 * x))))))) := by
  sorry

theorem proof_gap_exercise_1753_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) = ((((1 /. 2) * (1 - (Real.cos (6 * x)))) * (1 /. 4)) * ((3 * (Real.sin (2 * x))) - (Real.sin (6 * x))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) = ((((((3 /. 8) * (Real.sin (2 * x))) + ((3 /. 16) * (Real.sin (4 * x)))) - ((1 /. 8) * (Real.sin (6 * x)))) - ((3 /. 16) * (Real.sin (8 * x)))) + ((1 /. 16) * (Real.sin (12 * x))))))) := by
  sorry

theorem proof_gap_exercise_1753_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) = ((((1 /. 2) * (1 - (Real.cos (6 * x)))) * (1 /. 4)) * ((3 * (Real.sin (2 * x))) - (Real.sin (6 * x))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) = ((((((3 /. 8) * (Real.sin (2 * x))) + ((3 /. 16) * (Real.sin (4 * x)))) - ((1 /. 8) * (Real.sin (6 * x)))) - ((3 /. 16) * (Real.sin (8 * x)))) + ((1 /. 16) * (Real.sin (12 * x))))))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_3 x) = (((((((-(3 /. 16)) * (Real.cos (2 * x))) - ((3 /. 64) * (Real.cos (4 * x)))) + ((1 /. 48) * (Real.cos (6 * x)))) + ((3 /. 128) * (Real.cos (8 * x)))) - ((1 /. 192) * (Real.cos (12 * x)))) + C_1))))))}) := by
  sorry

theorem proof_gap_exercise_1753_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) = ((((1 /. 2) * (1 - (Real.cos (6 * x)))) * (1 /. 4)) * ((3 * (Real.sin (2 * x))) - (Real.sin (6 * x))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) = ((((((3 /. 8) * (Real.sin (2 * x))) + ((3 /. 16) * (Real.sin (4 * x)))) - ((1 /. 8) * (Real.sin (6 * x)))) - ((3 /. 16) * (Real.sin (8 * x)))) + ((1 /. 16) * (Real.sin (12 * x))))))))
  (h4 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.sin (3 * x)) ^ (2 : ℕ)) * ((Real.sin (2 * x)) ^ (3 : ℕ))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_3 x) = (((((((-(3 /. 16)) * (Real.cos (2 * x))) - ((3 /. 64) * (Real.cos (4 * x)))) + ((1 /. 48) * (Real.cos (6 * x)))) + ((3 /. 128) * (Real.cos (8 * x)))) - ((1 /. 192) * (Real.cos (12 * x)))) + C_1))))))}))
  : C ∈ (Set.univ : Set ℝ) := by
  sorry
