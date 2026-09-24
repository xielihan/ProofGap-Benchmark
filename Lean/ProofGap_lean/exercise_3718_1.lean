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

-- exercise: exercise_3718_1

theorem proof_gap_exercise_3718_1_1
  (F : (ℝ -> ℝ))
  (h1 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (Real.sin v_uCE_uB1)..(Real.cos v_uCE_uB1), ((Real.exp (v_uCE_uB1 * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((((-(Real.sin v_uCE_uB1)) * (Real.exp (v_uCE_uB1 * |((Real.sin v_uCE_uB1))|))) - ((Real.cos v_uCE_uB1) * (Real.exp (v_uCE_uB1 * |((Real.cos v_uCE_uB1))|)))) + (∫ x in (Real.sin v_uCE_uB1)..(Real.cos v_uCE_uB1), (((Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.exp (v_uCE_uB1 * (Real.rpow (1 - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))) * (1 : ℝ))))))) := by
  sorry
