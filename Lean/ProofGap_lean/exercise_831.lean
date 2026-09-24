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

-- exercise: exercise_831

theorem proof_gap_exercise_831_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = (x + ((x - 1) * (Real.arcsin (Real.rpow (x /. (x + 1)) (((2 : ℝ))⁻¹)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => f t) x) = ((1 + (Real.arcsin (Real.rpow (x /. (x + 1)) (((2 : ℝ))⁻¹)))) + ((x - 1) /. ((2 * (x + 1)) * (Real.rpow x (((2 : ℝ))⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_831_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = (x + ((x - 1) * (Real.arcsin (Real.rpow (x /. (x + 1)) (((2 : ℝ))⁻¹)))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => f t) x) = ((1 + (Real.arcsin (Real.rpow (x /. (x + 1)) (((2 : ℝ))⁻¹)))) + ((x - 1) /. ((2 * (x + 1)) * (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  : (iteratedDeriv 1 (fun t => f t) 1) = (1 + (Real.arcsin (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))) := by
  sorry

theorem proof_gap_exercise_831_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = (x + ((x - 1) * (Real.arcsin (Real.rpow (x /. (x + 1)) (((2 : ℝ))⁻¹)))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => f t) x) = ((1 + (Real.arcsin (Real.rpow (x /. (x + 1)) (((2 : ℝ))⁻¹)))) + ((x - 1) /. ((2 * (x + 1)) * (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  (h3 : (iteratedDeriv 1 (fun t => f t) 1) = (1 + (Real.arcsin (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))))
  : (Real.arcsin (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) = (Real.pi /. 4) := by
  sorry

theorem proof_gap_exercise_831_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((f x) = (x + ((x - 1) * (Real.arcsin (Real.rpow (x /. (x + 1)) (((2 : ℝ))⁻¹)))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => f t) x) = ((1 + (Real.arcsin (Real.rpow (x /. (x + 1)) (((2 : ℝ))⁻¹)))) + ((x - 1) /. ((2 * (x + 1)) * (Real.rpow x (((2 : ℝ))⁻¹)))))))))
  (h3 : (iteratedDeriv 1 (fun t => f t) 1) = (1 + (Real.arcsin (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))))
  (h4 : (Real.arcsin (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) = (Real.pi /. 4))
  : (iteratedDeriv 1 (fun t => f t) 1) = (1 + (Real.pi /. 4)) := by
  sorry
