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

-- exercise: exercise_1100

theorem proof_gap_exercise_1100_1
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (v_uCE_u94_x : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_u94_x ∈ (Set.univ : Set ℝ))
  (h3 : f = (fun (x : ℝ) => (Real.sin x)))
  (h4 : x_0 = (Real.pi /. 6))
  (h5 : v_uCE_u94_x = (-(Real.pi /. 180)))
  : ((29 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x) := by
  sorry

theorem proof_gap_exercise_1100_2
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (v_uCE_u94_x : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_u94_x ∈ (Set.univ : Set ℝ))
  (h3 : f = (fun (x : ℝ) => (Real.sin x)))
  (h4 : x_0 = (Real.pi /. 6))
  (h5 : v_uCE_u94_x = (-(Real.pi /. 180)))
  (h6 : ((29 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos x_0) := by
  sorry

theorem proof_gap_exercise_1100_3
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (v_uCE_u94_x : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_u94_x ∈ (Set.univ : Set ℝ))
  (h3 : f = (fun (x : ℝ) => (Real.sin x)))
  (h4 : x_0 = (Real.pi /. 6))
  (h5 : v_uCE_u94_x = (-(Real.pi /. 180)))
  (h6 : ((29 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h7 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos x_0))
  : (Real.cos x_0) = (Real.cos (Real.pi /. 6)) := by
  sorry

theorem proof_gap_exercise_1100_4
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (v_uCE_u94_x : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_u94_x ∈ (Set.univ : Set ℝ))
  (h3 : f = (fun (x : ℝ) => (Real.sin x)))
  (h4 : x_0 = (Real.pi /. 6))
  (h5 : v_uCE_u94_x = (-(Real.pi /. 180)))
  (h6 : ((29 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h7 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos x_0))
  (h8 : (Real.cos x_0) = (Real.cos (Real.pi /. 6)))
  : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos (Real.pi /. 6)) := by
  sorry

theorem proof_gap_exercise_1100_5
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (v_uCE_u94_x : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_u94_x ∈ (Set.univ : Set ℝ))
  (h3 : f = (fun (x : ℝ) => (Real.sin x)))
  (h4 : x_0 = (Real.pi /. 6))
  (h5 : v_uCE_u94_x = (-(Real.pi /. 180)))
  (h6 : ((29 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h7 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos x_0))
  (h8 : (Real.cos x_0) = (Real.cos (Real.pi /. 6)))
  (h9 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos (Real.pi /. 6)))
  : (Real.sin ((29 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)) := by
  sorry

theorem proof_gap_exercise_1100_6
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (v_uCE_u94_x : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_u94_x ∈ (Set.univ : Set ℝ))
  (h3 : f = (fun (x : ℝ) => (Real.sin x)))
  (h4 : x_0 = (Real.pi /. 6))
  (h5 : v_uCE_u94_x = (-(Real.pi /. 180)))
  (h6 : ((29 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h7 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos x_0))
  (h8 : (Real.cos x_0) = (Real.cos (Real.pi /. 6)))
  (h9 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos (Real.pi /. 6)))
  (h10 : (Real.sin ((29 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)))
  : (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ v_uCE_uB5))) := by
  sorry

theorem proof_gap_exercise_1100_7
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (v_uCE_u94_x : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_u94_x ∈ (Set.univ : Set ℝ))
  (h3 : f = (fun (x : ℝ) => (Real.sin x)))
  (h4 : x_0 = (Real.pi /. 6))
  (h5 : v_uCE_u94_x = (-(Real.pi /. 180)))
  (h6 : ((29 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h7 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos x_0))
  (h8 : (Real.cos x_0) = (Real.cos (Real.pi /. 6)))
  (h9 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos (Real.pi /. 6)))
  (h10 : (Real.sin ((29 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)))
  (h11 : (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ v_uCE_uB5))))
  : (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|((Real.sin ((29 * Real.pi) /. 180)) - ((Real.sin (Real.pi /. 6)) - ((Real.pi /. 180) * (Real.cos (Real.pi /. 6)))))| ≤ v_uCE_uB5))) := by
  sorry

theorem proof_gap_exercise_1100_8
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (v_uCE_u94_x : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_u94_x ∈ (Set.univ : Set ℝ))
  (h3 : f = (fun (x : ℝ) => (Real.sin x)))
  (h4 : x_0 = (Real.pi /. 6))
  (h5 : v_uCE_u94_x = (-(Real.pi /. 180)))
  (h6 : ((29 * Real.pi) /. 180) = (x_0 + v_uCE_u94_x))
  (h7 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos x_0))
  (h8 : (Real.cos x_0) = (Real.cos (Real.pi /. 6)))
  (h9 : (iteratedDeriv 1 (fun t => f t) x_0) = (Real.cos (Real.pi /. 6)))
  (h10 : (Real.sin ((29 * Real.pi) /. 180)) = (f (x_0 + v_uCE_u94_x)))
  (h11 : (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ v_uCE_uB5))))
  (h12 : (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|((Real.sin ((29 * Real.pi) /. 180)) - ((Real.sin (Real.pi /. 6)) - ((Real.pi /. 180) * (Real.cos (Real.pi /. 6)))))| ≤ v_uCE_uB5))))
  : (exists (v_uCE_uB5 : ℝ), ((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (|((Real.sin ((29 * Real.pi) /. 180)) - (((04849 : ℝ) /. (10000 : ℝ))))| ≤ v_uCE_uB5))) := by
  sorry
