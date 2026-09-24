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

-- exercise: exercise_3718_2

theorem proof_gap_exercise_3718_2_1
  (F : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : (forall (v_uCE_uB1 : ℝ), ((((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≠ 0)) ∧ (0 ∉ (Set.Icc (a + v_uCE_uB1) (b + v_uCE_uB1)))) → ((F v_uCE_uB1) = (∫ x in (a + v_uCE_uB1)..(b + v_uCE_uB1), (((Real.sin (v_uCE_uB1 * x)) /. x) * (1 : ℝ)))))))
  : (forall (v_uCE_uB1 : ℝ), ((((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≠ 0)) ∧ (0 ∉ (Set.Icc (a + v_uCE_uB1) (b + v_uCE_uB1)))) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((((Real.sin (v_uCE_uB1 * (b + v_uCE_uB1))) /. (b + v_uCE_uB1)) - ((Real.sin (v_uCE_uB1 * (a + v_uCE_uB1))) /. (a + v_uCE_uB1))) + (∫ x in (a + v_uCE_uB1)..(b + v_uCE_uB1), ((Real.cos (v_uCE_uB1 * x)) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3718_2_2
  (F : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : (forall (v_uCE_uB1 : ℝ), ((((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≠ 0)) ∧ (0 ∉ (Set.Icc (a + v_uCE_uB1) (b + v_uCE_uB1)))) → ((F v_uCE_uB1) = (∫ x in (a + v_uCE_uB1)..(b + v_uCE_uB1), (((Real.sin (v_uCE_uB1 * x)) /. x) * (1 : ℝ)))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≠ 0)) ∧ (0 ∉ (Set.Icc (a + v_uCE_uB1) (b + v_uCE_uB1)))) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((((Real.sin (v_uCE_uB1 * (b + v_uCE_uB1))) /. (b + v_uCE_uB1)) - ((Real.sin (v_uCE_uB1 * (a + v_uCE_uB1))) /. (a + v_uCE_uB1))) + (∫ x in (a + v_uCE_uB1)..(b + v_uCE_uB1), ((Real.cos (v_uCE_uB1 * x)) * (1 : ℝ))))))))
  : (forall (v_uCE_uB1 : ℝ), ((((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≠ 0)) ∧ (0 ∉ (Set.Icc (a + v_uCE_uB1) (b + v_uCE_uB1)))) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((((1 /. v_uCE_uB1) + (1 /. (b + v_uCE_uB1))) * (Real.sin (v_uCE_uB1 * (b + v_uCE_uB1)))) - (((1 /. v_uCE_uB1) + (1 /. (a + v_uCE_uB1))) * (Real.sin (v_uCE_uB1 * (a + v_uCE_uB1)))))))) := by
  sorry
