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

-- exercise: exercise_1104_1

theorem proof_gap_exercise_1104_1_1
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x) := by
  sorry

theorem proof_gap_exercise_1104_1_2
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1104_1_3
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h9 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_1104_1_4
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h9 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h10 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a := by
  sorry

theorem proof_gap_exercise_1104_1_5
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h9 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h10 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h11 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1104_1_6
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h9 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h10 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h11 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h12 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  : (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) := by
  sorry

theorem proof_gap_exercise_1104_1_7
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h9 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h10 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h11 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h12 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  (h13 : (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))
  (h14 : a = 2)
  (h15 : x = 1)
  : |((Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) - (2 + (1 /. 4)))| ≤ 1 := by
  sorry

theorem proof_gap_exercise_1104_1_8
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h9 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h10 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h11 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h12 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  (h13 : (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))
  (h14 : |((Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) - (2 + (1 /. 4)))| ≤ 1)
  : (2 + (1 /. 4)) = (((225 : ℝ) /. (100 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1104_1_9
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h9 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h10 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h11 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h12 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  (h13 : (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))
  (h14 : |((Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) - (2 + (1 /. 4)))| ≤ 1)
  (h15 : (2 + (1 /. 4)) = (((225 : ℝ) /. (100 : ℝ))))
  : (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) = (((224 : ℝ) /. (100 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1104_1_10
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : ((a ^ (2 : ℕ)) + x) ≥ 0)
  (h5 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h6 : y_0 = (a ^ (2 : ℕ)))
  (h7 : v_uCE_u94_y = x)
  (h8 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h9 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h10 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h11 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h12 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  (h13 : (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))
  (h14 : |((Real.rpow (((2 : ℕ) ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) - (2 + (1 /. 4)))| ≤ 1)
  (h15 : (2 + (1 /. 4)) = (((225 : ℝ) /. (100 : ℝ))))
  (h16 : (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) = (((224 : ℝ) /. (100 : ℝ))))
  : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)) := by
  sorry
