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

-- exercise: exercise_1141

theorem proof_gap_exercise_1141_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (Real.cos t))))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (Real.sin t))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin t) ≠ 0)) → ((((lpFunDeri y x) t) = ((a * (Real.cos t)) /. ((-a) * (Real.sin t)))) ∧ (((a * (Real.cos t)) /. ((-a) * (Real.sin t))) = (-((1 : ℝ) /. (Real.tan t))))))) := by
  sorry

theorem proof_gap_exercise_1141_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (Real.cos t))))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (Real.sin t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin t) ≠ 0)) → ((((lpFunDeri y x) t) = ((a * (Real.cos t)) /. ((-a) * (Real.sin t)))) ∧ (((a * (Real.cos t)) /. ((-a) * (Real.sin t))) = (-((1 : ℝ) /. (Real.tan t))))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin t) ≠ 0)) → ((((lpFunDeri (lpFunDeri y x) x) t) = ((1 /. ((Real.sin t) ^ (2 : ℕ))) /. ((-a) * (Real.sin t)))) ∧ (((1 /. ((Real.sin t) ^ (2 : ℕ))) /. ((-a) * (Real.sin t))) = (-(1 /. (a * ((Real.sin t) ^ (3 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_1141_3
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a ≠ 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (Real.cos t))))))
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (Real.sin t))))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin t) ≠ 0)) → ((((lpFunDeri y x) t) = ((a * (Real.cos t)) /. ((-a) * (Real.sin t)))) ∧ (((a * (Real.cos t)) /. ((-a) * (Real.sin t))) = (-((1 : ℝ) /. (Real.tan t))))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((Real.sin t) ≠ 0)) → ((((lpFunDeri (lpFunDeri y x) x) t) = ((1 /. ((Real.sin t) ^ (2 : ℕ))) /. ((-a) * (Real.sin t)))) ∧ (((1 /. ((Real.sin t) ^ (2 : ℕ))) /. ((-a) * (Real.sin t))) = (-(1 /. (a * ((Real.sin t) ^ (3 : ℕ))))))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (t ≠ (k * Real.pi))))) → ((((lpFunDeri (lpFunDeri (lpFunDeri y x) x) x) t) = (((3 * (Real.cos t)) /. (a * ((Real.sin t) ^ (4 : ℕ)))) /. ((-a) * (Real.sin t)))) ∧ ((((3 * (Real.cos t)) /. (a * ((Real.sin t) ^ (4 : ℕ)))) /. ((-a) * (Real.sin t))) = (-((3 * (Real.cos t)) /. ((a ^ (2 : ℕ)) * ((Real.sin t) ^ (5 : ℕ))))))))) := by
  sorry
