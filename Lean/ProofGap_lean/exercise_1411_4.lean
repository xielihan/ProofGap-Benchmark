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

-- exercise: exercise_1411_4

theorem proof_gap_exercise_1411_4_1
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x /. 100)) > 0))
  (h2 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h3 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  : |((Real.log (1 + (x /. 100))) - ((x /. 100) - ((x ^ (2 : ℕ)) /. 20000)))| ≤ ((x ^ (2 : ℕ)) /. 20000) := by
  sorry

theorem proof_gap_exercise_1411_4_2
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x /. 100)) > 0))
  (h2 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h3 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h4 : |((Real.log (1 + (x /. 100))) - ((x /. 100) - ((x ^ (2 : ℕ)) /. 20000)))| ≤ ((x ^ (2 : ℕ)) /. 20000))
  : |(((Real.log (2 : ℝ)) /. (Real.log (1 + (x /. 100)))) - ((Real.log (2 : ℝ)) /. (x /. 100)))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1411_4_3
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x /. 100)) > 0))
  (h2 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h3 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h4 : |((Real.log (1 + (x /. 100))) - ((x /. 100) - ((x ^ (2 : ℕ)) /. 20000)))| ≤ ((x ^ (2 : ℕ)) /. 20000))
  (h5 : |(((Real.log (2 : ℝ)) /. (Real.log (1 + (x /. 100)))) - ((Real.log (2 : ℝ)) /. (x /. 100)))| ≤ v_uCE_uB5)
  : ((Real.log (2 : ℝ)) /. (x /. 100)) = ((100 * (Real.log (2 : ℝ))) /. x) := by
  sorry

theorem proof_gap_exercise_1411_4_4
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x /. 100)) > 0))
  (h2 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h3 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h4 : |((Real.log (1 + (x /. 100))) - ((x /. 100) - ((x ^ (2 : ℕ)) /. 20000)))| ≤ ((x ^ (2 : ℕ)) /. 20000))
  (h5 : |(((Real.log (2 : ℝ)) /. (Real.log (1 + (x /. 100)))) - ((Real.log (2 : ℝ)) /. (x /. 100)))| ≤ v_uCE_uB5)
  (h6 : ((Real.log (2 : ℝ)) /. (x /. 100)) = ((100 * (Real.log (2 : ℝ))) /. x))
  : |(((100 * (Real.log (2 : ℝ))) /. x) - (70 /. x))| ≤ v_uCE_uB5 := by
  sorry

theorem proof_gap_exercise_1411_4_5
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((1 + (x /. 100)) > 0))
  (h2 : (v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0))
  (h3 : |(|(x)| - 0)| ≤ v_uCE_uB5)
  (h4 : |((Real.log (1 + (x /. 100))) - ((x /. 100) - ((x ^ (2 : ℕ)) /. 20000)))| ≤ ((x ^ (2 : ℕ)) /. 20000))
  (h5 : |(((Real.log (2 : ℝ)) /. (Real.log (1 + (x /. 100)))) - ((Real.log (2 : ℝ)) /. (x /. 100)))| ≤ v_uCE_uB5)
  (h6 : ((Real.log (2 : ℝ)) /. (x /. 100)) = ((100 * (Real.log (2 : ℝ))) /. x))
  (h7 : |(((100 * (Real.log (2 : ℝ))) /. x) - (70 /. x))| ≤ v_uCE_uB5)
  : |(((Real.log (2 : ℝ)) /. (Real.log (1 + (x /. 100)))) - (70 /. x))| ≤ v_uCE_uB5 := by
  sorry
