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

-- exercise: exercise_1109

theorem proof_gap_exercise_1109_1
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_u94_x : ℝ)
  (v_uCE_uB4 : ℝ)
  (E : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ ((x + v_uCE_u94_x) > 0))
  (h3 : (v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 ≥ 0))
  (h4 : E ∈ (Set.univ : Set ℝ))
  (h5 : v_uCE_uB4 = |((v_uCE_u94_x /. x))|)
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f t) = (Real.logb 10 t)))))
  : E = |(((Real.logb 10 (x + v_uCE_u94_x)) - (Real.logb 10 x)))| := by
  sorry

theorem proof_gap_exercise_1109_2
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_u94_x : ℝ)
  (v_uCE_uB4 : ℝ)
  (E : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ ((x + v_uCE_u94_x) > 0))
  (h3 : (v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 ≥ 0))
  (h4 : E ∈ (Set.univ : Set ℝ))
  (h5 : v_uCE_uB4 = |((v_uCE_u94_x /. x))|)
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f t) = (Real.logb 10 t)))))
  (h7 : E = |(((Real.logb 10 (x + v_uCE_u94_x)) - (Real.logb 10 x)))|)
  : E = |((Real.logb 10 (1 + (v_uCE_u94_x /. x))))| := by
  sorry

theorem proof_gap_exercise_1109_3
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_u94_x : ℝ)
  (v_uCE_uB4 : ℝ)
  (E : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ ((x + v_uCE_u94_x) > 0))
  (h3 : (v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 ≥ 0))
  (h4 : E ∈ (Set.univ : Set ℝ))
  (h5 : v_uCE_uB4 = |((v_uCE_u94_x /. x))|)
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f t) = (Real.logb 10 t)))))
  (h7 : E = |(((Real.logb 10 (x + v_uCE_u94_x)) - (Real.logb 10 x)))|)
  (h8 : E = |((Real.logb 10 (1 + (v_uCE_u94_x /. x))))|)
  : ((v_uCE_u94_x /. x) = v_uCE_uB4) → (E = |((Real.logb 10 (1 + v_uCE_uB4)))|) := by
  sorry

theorem proof_gap_exercise_1109_4
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_u94_x : ℝ)
  (v_uCE_uB4 : ℝ)
  (E : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ ((x + v_uCE_u94_x) > 0))
  (h3 : (v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 ≥ 0))
  (h4 : E ∈ (Set.univ : Set ℝ))
  (h5 : v_uCE_uB4 = |((v_uCE_u94_x /. x))|)
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f t) = (Real.logb 10 t)))))
  (h7 : E = |(((Real.logb 10 (x + v_uCE_u94_x)) - (Real.logb 10 x)))|)
  (h8 : E = |((Real.logb 10 (1 + (v_uCE_u94_x /. x))))|)
  (h9 : ((v_uCE_u94_x /. x) = v_uCE_uB4) → (E = |((Real.logb 10 (1 + v_uCE_uB4)))|))
  : ((v_uCE_u94_x /. x) = v_uCE_uB4) → (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|(E - ((1 /. (Real.log (10 : ℝ))) * v_uCE_uB4))| ≤ v_uCE_uB5))) := by
  sorry

theorem proof_gap_exercise_1109_5
  (f : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_u94_x : ℝ)
  (v_uCE_uB4 : ℝ)
  (E : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ ((x + v_uCE_u94_x) > 0))
  (h3 : (v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 ≥ 0))
  (h4 : E ∈ (Set.univ : Set ℝ))
  (h5 : v_uCE_uB4 = |((v_uCE_u94_x /. x))|)
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ∈ ({x_1 : ℝ | 0 < x_1}))) → ((f t) = (Real.logb 10 t)))))
  (h7 : E = |(((Real.logb 10 (x + v_uCE_u94_x)) - (Real.logb 10 x)))|)
  (h8 : E = |((Real.logb 10 (1 + (v_uCE_u94_x /. x))))|)
  (h9 : ((v_uCE_u94_x /. x) = v_uCE_uB4) → (E = |((Real.logb 10 (1 + v_uCE_uB4)))|))
  (h10 : ((v_uCE_u94_x /. x) = v_uCE_uB4) → (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|(E - ((1 /. (Real.log (10 : ℝ))) * v_uCE_uB4))| ≤ v_uCE_uB5))))
  : ((v_uCE_u94_x /. x) = v_uCE_uB4) → (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|(E - ((((04343 : ℝ) /. (10000 : ℝ))) * v_uCE_uB4))| ≤ v_uCE_uB5))) := by
  sorry
