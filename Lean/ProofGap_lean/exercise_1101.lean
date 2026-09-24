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

-- exercise: exercise_1101

theorem proof_gap_exercise_1101_1
  (h1 : f = (fun (x : ℝ) => (Real.cos x)))
  (h2 : x_0 = ((5 * Real.pi) /. 6))
  (h3 : v_uCE_u94_x = (Real.pi /. 180))
  : ((151 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x) := by
  sorry

theorem proof_gap_exercise_1101_2
  (h1 : f = (fun (x : ℝ) => (Real.cos x)))
  (h2 : x_0 = ((5 * Real.pi) /. 6))
  (h3 : v_uCE_u94_x = (Real.pi /. 180))
  (h4 : ((151 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  : (Real.cos ((151 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)) := by
  sorry

theorem proof_gap_exercise_1101_3
  (h1 : f = (fun (x : ℝ) => (Real.cos x)))
  (h2 : x_0 = ((5 * Real.pi) /. 6))
  (h3 : v_uCE_u94_x = (Real.pi /. 180))
  (h4 : ((151 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h5 : (Real.cos ((151 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)))
  : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1101_4
  (h1 : f = (fun (x : ℝ) => (Real.cos x)))
  (h2 : x_0 = ((5 * Real.pi) /. 6))
  (h3 : v_uCE_u94_x = (Real.pi /. 180))
  (h4 : ((151 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h5 : (Real.cos ((151 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)))
  (h6 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  : (iteratedDeriv 1 (fun t => f t) x_0) = (-(Real.sin x_0)) := by
  sorry

theorem proof_gap_exercise_1101_5
  (h1 : f = (fun (x : ℝ) => (Real.cos x)))
  (h2 : x_0 = ((5 * Real.pi) /. 6))
  (h3 : v_uCE_u94_x = (Real.pi /. 180))
  (h4 : ((151 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h5 : (Real.cos ((151 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)))
  (h6 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h7 : (iteratedDeriv 1 (fun t => f t) x_0) = (-(Real.sin x_0)))
  : |((Real.cos ((151 * Real.pi) /. 180)) - ((Real.cos ((5 * Real.pi) /. 6)) - ((Real.sin ((5 * Real.pi) /. 6)) * (Real.pi /. 180))))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1101_6
  (h1 : f = (fun (x : ℝ) => (Real.cos x)))
  (h2 : x_0 = ((5 * Real.pi) /. 6))
  (h3 : v_uCE_u94_x = (Real.pi /. 180))
  (h4 : ((151 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h5 : (Real.cos ((151 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)))
  (h6 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h7 : (iteratedDeriv 1 (fun t => f t) x_0) = (-(Real.sin x_0)))
  (h8 : |((Real.cos ((151 * Real.pi) /. 180)) - ((Real.cos ((5 * Real.pi) /. 6)) - ((Real.sin ((5 * Real.pi) /. 6)) * (Real.pi /. 180))))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  : (Real.cos ((151 * Real.pi) /. 180)) = (-(((08748 : ℝ) /. (10000 : ℝ)))) := by
  sorry
