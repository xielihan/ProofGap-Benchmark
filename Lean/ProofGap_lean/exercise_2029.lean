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

-- exercise: exercise_2029

theorem proof_gap_exercise_2029_1
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.sin x) ^ (2 : ℕ)) /. (1 + ((Real.sin x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 - (1 /. (1 + ((Real.sin x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) := by
  sorry

theorem proof_gap_exercise_2029_2
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.sin x) ^ (2 : ℕ)) /. (1 + ((Real.sin x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 - (1 /. (1 + ((Real.sin x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((1 - (1 /. (1 + ((Real.sin x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. ((((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)) + ((Real.tan x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan t)) x))) ∧ ((F_7 x) = (x - (F_5 x)))))))}) := by
  sorry

theorem proof_gap_exercise_2029_3
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.sin x) ^ (2 : ℕ)) /. (1 + ((Real.sin x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 - (1 /. (1 + ((Real.sin x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h3 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((1 - (1 /. (1 + ((Real.sin x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. ((((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)) + ((Real.tan x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan t)) x))) ∧ ((F_7 x) = (x - (F_5 x)))))))}))
  : ({F_10 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_8 t) x) = ((1 /. ((((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)) + ((Real.tan x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan t)) x))) ∧ ((F_10 x) = (x - (F_8 x)))))))}) = ({F_13 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_11 t) x) = ((1 /. (1 + (2 * ((Real.tan x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => (Real.tan t)) x))) ∧ ((F_13 x) = (x - (F_11 x)))))))}) := by
  sorry

theorem proof_gap_exercise_2029_4
  (C : ℝ)
  (h1 : C ∈ (Set.univ : Set ℝ))
  (h2 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((((Real.sin x) ^ (2 : ℕ)) /. (1 + ((Real.sin x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((1 - (1 /. (1 + ((Real.sin x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h3 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((1 - (1 /. (1 + ((Real.sin x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_7 : (ℝ -> ℝ) | (exists (F_5 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. ((((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)) + ((Real.tan x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan t)) x))) ∧ ((F_7 x) = (x - (F_5 x)))))))}))
  (h4 : ({F_10 : (ℝ -> ℝ) | (exists (F_8 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_8 t) x) = ((1 /. ((((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)) + ((Real.tan x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan t)) x))) ∧ ((F_10 x) = (x - (F_8 x)))))))}) = ({F_13 : (ℝ -> ℝ) | (exists (F_11 : (ℝ -> ℝ)), (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F_11 t) x) = ((1 /. (1 + (2 * ((Real.tan x) ^ (2 : ℕ))))) * (iteratedDeriv 1 (fun t => (Real.tan t)) x))) ∧ ((F_13 x) = (x - (F_11 x)))))))}))
  : ({F_14 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_14 t) x) = ((((Real.sin x) ^ (2 : ℕ)) /. (1 + ((Real.sin x) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_15 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_15 x) = ((x - ((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (Real.arctan ((Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)) * (Real.tan x))))) + C_1))))))}) := by
  sorry
