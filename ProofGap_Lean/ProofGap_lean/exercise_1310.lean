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

-- exercise: exercise_1310

theorem proof_gap_exercise_1310_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((x t) = (a * (t - (Real.sin t)))) ∧ ((y t) = (a * (1 - (Real.cos t))))))))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (t ≠ ((2 * k) * Real.pi))) ∧ (k ∈ (Set.univ : Set ℤ))) → ((((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))) ∧ (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2))))))))) := by
  sorry

theorem proof_gap_exercise_1310_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → (((x t) = (a * (t - (Real.sin t)))) ∧ ((y t) = (a * (1 - (Real.cos t))))))))
  (h3 : (forall (k : ℤ) (t : ℝ), (((((k ∈ (Set.univ : Set ℤ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (((2 * k) * Real.pi) < t)) ∧ (t < ((2 * (k + 1)) * Real.pi))) → ((((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))) ∧ (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2))))))))
  : (forall (t : ℝ) (k : ℤ), (((((t ∈ (Set.univ : Set ℝ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (((2 * k) * Real.pi) < t)) ∧ (t < ((2 * (k + 1)) * Real.pi))) → (((((lpFunDeri (lpFunDeri y x) x) t) = ((((iteratedDeriv 1 (fun t_1 => x t_1) t) * (iteratedDeriv 2 (fun t_1 => y t_1) t)) - ((iteratedDeriv 2 (fun t_1 => x t_1) t) * (iteratedDeriv 1 (fun t_1 => y t_1) t))) /. ((iteratedDeriv 1 (fun t_1 => x t_1) t) ^ (3 : ℕ)))) ∧ (((((iteratedDeriv 1 (fun t_1 => x t_1) t) * (iteratedDeriv 2 (fun t_1 => y t_1) t)) - ((iteratedDeriv 2 (fun t_1 => x t_1) t) * (iteratedDeriv 1 (fun t_1 => y t_1) t))) /. ((iteratedDeriv 1 (fun t_1 => x t_1) t) ^ (3 : ℕ))) = (-((((1 : ℝ) /. (Real.sin (t /. 2))) ^ (2 : ℕ)) /. ((2 * a) * (1 - (Real.cos t))))))) ∧ ((-((((1 : ℝ) /. (Real.sin (t /. 2))) ^ (2 : ℕ)) /. ((2 * a) * (1 - (Real.cos t))))) < 0)))) := by
  sorry
