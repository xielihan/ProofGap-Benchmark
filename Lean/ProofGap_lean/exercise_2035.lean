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

-- exercise: exercise_2035

theorem proof_gap_exercise_2035_1
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (2 * x)) ≠ 0))))
  : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((Real.sin x) ^ (4 : ℕ)) + ((Real.cos x) ^ (4 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) := by
  sorry

theorem proof_gap_exercise_2035_2
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (2 * x)) ≠ 0))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((Real.sin x) ^ (4 : ℕ)) + ((Real.cos x) ^ (4 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. ((2 * (((1 : ℝ) /. (Real.cos (2 * x))) ^ (2 : ℕ))) - ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}) := by
  sorry

theorem proof_gap_exercise_2035_3
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (2 * x)) ≠ 0))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((Real.sin x) ^ (4 : ℕ)) + ((Real.cos x) ^ (4 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. ((2 * (((1 : ℝ) /. (Real.cos (2 * x))) ^ (2 : ℕ))) - ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}))
  : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = ((1 /. ((2 * (((1 : ℝ) /. (Real.cos (2 * x))) ^ (2 : ℕ))) - ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}) = ({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = ((1 /. (2 + ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}) := by
  sorry

theorem proof_gap_exercise_2035_4
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (2 * x)) ≠ 0))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((Real.sin x) ^ (4 : ℕ)) + ((Real.cos x) ^ (4 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. ((2 * (((1 : ℝ) /. (Real.cos (2 * x))) ^ (2 : ℕ))) - ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}))
  (h5 : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = ((1 /. ((2 * (((1 : ℝ) /. (Real.cos (2 * x))) ^ (2 : ℕ))) - ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}) = ({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = ((1 /. (2 + ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}))
  : ({F_8 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_8 t) x) = ((1 /. (2 + ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_9 x) = (((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (Real.arctan ((Real.tan (2 * x)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))) + C))))))}) := by
  sorry

theorem proof_gap_exercise_2035_5
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((Real.cos (2 * x)) ≠ 0))))
  (h3 : ({F_2 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_2 t) x) = ((1 /. (((Real.sin x) ^ (4 : ℕ)) + ((Real.cos x) ^ (4 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_3 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_3 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}))
  (h4 : ({F_4 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_4 t) x) = ((2 /. (2 - ((Real.sin (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_5 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_5 t) x) = ((1 /. ((2 * (((1 : ℝ) /. (Real.cos (2 * x))) ^ (2 : ℕ))) - ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}))
  (h5 : ({F_6 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_6 t) x) = ((1 /. ((2 * (((1 : ℝ) /. (Real.cos (2 * x))) ^ (2 : ℕ))) - ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}) = ({F_7 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_7 t) x) = ((1 /. (2 + ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}))
  (h6 : ({F_8 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_8 t) x) = ((1 /. (2 + ((Real.tan (2 * x)) ^ (2 : ℕ)))) * (iteratedDeriv 1 (fun t => (Real.tan (2 * t))) x)))))}) = ({F_9 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_9 x) = (((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (Real.arctan ((Real.tan (2 * x)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))) + C))))))}))
  : ({F_10 : (ℝ -> ℝ) | (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F_10 t) x) = ((1 /. (((Real.sin x) ^ (4 : ℕ)) + ((Real.cos x) ^ (4 : ℕ)))) * (iteratedDeriv 1 (fun t => t) x)))))}) = ({F_11 : (ℝ -> ℝ) | (exists (C : ℝ), ((C ∈ (Set.univ : Set ℝ)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F_11 x) = (((1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) * (Real.arctan ((Real.tan (2 * x)) /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))) + C))))))}) := by
  sorry
