import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_1103

theorem proof_gap_exercise_1103_1
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_1103_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  : (Real.logb 10 (10 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_1103_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  : (((11 : ℝ) /. (10 : ℝ))) = (x_0 + v_uCE_u94_x) := by
  sorry

theorem proof_gap_exercise_1103_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : (((11 : ℝ) /. (10 : ℝ))) = (x_0 + v_uCE_u94_x))
  : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1103_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : (((11 : ℝ) /. (10 : ℝ))) = (x_0 + v_uCE_u94_x))
  (h7 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  : (iteratedDeriv 1 (fun t => f t) x_0) = (1 /. (x_0 * (Real.log (10 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_1103_6
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : (((11 : ℝ) /. (10 : ℝ))) = (x_0 + v_uCE_u94_x))
  (h7 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) x_0) = (1 /. (x_0 * (Real.log (10 : ℝ)))))
  : |((Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) - ((Real.logb 10 (1 : ℝ)) + ((((01 : ℝ) /. (10 : ℝ))) /. (Real.log (10 : ℝ)))))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1103_7
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : (((11 : ℝ) /. (10 : ℝ))) = (x_0 + v_uCE_u94_x))
  (h7 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) x_0) = (1 /. (x_0 * (Real.log (10 : ℝ)))))
  (h9 : |((Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) - ((Real.logb 10 (1 : ℝ)) + ((((01 : ℝ) /. (10 : ℝ))) /. (Real.log (10 : ℝ)))))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  : (Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) = ((((01 : ℝ) /. (10 : ℝ))) /. (((23026 : ℝ) /. (10000 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_1103_8
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : (((11 : ℝ) /. (10 : ℝ))) = (x_0 + v_uCE_u94_x))
  (h7 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) x_0) = (1 /. (x_0 * (Real.log (10 : ℝ)))))
  (h9 : |((Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) - ((Real.logb 10 (1 : ℝ)) + ((((01 : ℝ) /. (10 : ℝ))) /. (Real.log (10 : ℝ)))))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h10 : (Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) = ((((01 : ℝ) /. (10 : ℝ))) /. (((23026 : ℝ) /. (10000 : ℝ)))))
  : ((((01 : ℝ) /. (10 : ℝ))) /. (((23026 : ℝ) /. (10000 : ℝ)))) = (((00434 : ℝ) /. (10000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1103_9
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : (((11 : ℝ) /. (10 : ℝ))) = (x_0 + v_uCE_u94_x))
  (h7 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) x_0) = (1 /. (x_0 * (Real.log (10 : ℝ)))))
  (h9 : |((Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) - ((Real.logb 10 (1 : ℝ)) + ((((01 : ℝ) /. (10 : ℝ))) /. (Real.log (10 : ℝ)))))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h10 : (Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) = ((((01 : ℝ) /. (10 : ℝ))) /. (((23026 : ℝ) /. (10000 : ℝ)))))
  (h11 : ((((01 : ℝ) /. (10 : ℝ))) /. (((23026 : ℝ) /. (10000 : ℝ)))) = (((00434 : ℝ) /. (10000 : ℝ))))
  : (Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) = (((00434 : ℝ) /. (10000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1103_10
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) → (((f : ℝ → _) x) = (Real.logb 10 x))))
  (h2 : x_0 = 1)
  (h3 : v_uCE_u94_x = (((01 : ℝ) /. (10 : ℝ))))
  (h4 : (Real.logb 10 (11 : ℝ)) = ((Real.logb 10 (10 : ℝ)) + (Real.logb 10 (((11 : ℝ) /. (10 : ℝ))))))
  (h5 : (Real.logb 10 (10 : ℝ)) = 1)
  (h6 : (((11 : ℝ) /. (10 : ℝ))) = (x_0 + v_uCE_u94_x))
  (h7 : |((f (x_0 + v_uCE_u94_x)) - ((f x_0) + ((iteratedDeriv 1 (fun t => f t) x_0) * v_uCE_u94_x)))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) x_0) = (1 /. (x_0 * (Real.log (10 : ℝ)))))
  (h9 : |((Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) - ((Real.logb 10 (1 : ℝ)) + ((((01 : ℝ) /. (10 : ℝ))) /. (Real.log (10 : ℝ)))))| ≤ (|(v_uCE_u94_x)| ^ (2 : ℕ)))
  (h10 : (Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) = ((((01 : ℝ) /. (10 : ℝ))) /. (((23026 : ℝ) /. (10000 : ℝ)))))
  (h11 : ((((01 : ℝ) /. (10 : ℝ))) /. (((23026 : ℝ) /. (10000 : ℝ)))) = (((00434 : ℝ) /. (10000 : ℝ))))
  (h12 : (Real.logb 10 (((11 : ℝ) /. (10 : ℝ)))) = (((00434 : ℝ) /. (10000 : ℝ))))
  : (Real.logb 10 (11 : ℝ)) = (((10434 : ℝ) /. (10000 : ℝ))) := by
  sorry
