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

-- exercise: exercise_1104_2

theorem proof_gap_exercise_1104_2_1
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x) := by
  sorry

theorem proof_gap_exercise_1104_2_2
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1104_2_3
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h7 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_1104_2_4
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h7 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a := by
  sorry

theorem proof_gap_exercise_1104_2_5
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h7 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h9 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1104_2_6
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h7 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h9 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h10 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  : (Real.rpow (34 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)) := by
  sorry

theorem proof_gap_exercise_1104_2_7
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h7 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h9 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h10 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  (h11 : (Real.rpow (34 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)))
  : |((Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)) - (6 - (2 /. (2 * 6))))| ≤ (|((-(2 : ℤ)))| ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1104_2_8
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h7 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h9 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h10 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  (h11 : (Real.rpow (34 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)))
  (h12 : |((Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)) - (6 - (2 /. (2 * 6))))| ≤ (|((-(2 : ℤ)))| ^ (2 : ℕ)))
  : (6 - (2 /. (2 * 6))) = (((5833 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1104_2_9
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h7 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h9 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h10 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  (h11 : (Real.rpow (34 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)))
  (h12 : |((Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)) - (6 - (2 /. (2 * 6))))| ≤ (|((-(2 : ℤ)))| ^ (2 : ℕ)))
  (h13 : (6 - (2 /. (2 * 6))) = (((5833 : ℝ) /. (1000 : ℝ))))
  : (Real.rpow (34 : ℝ) (((2 : ℝ))⁻¹)) = (((5831 : ℝ) /. (1000 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1104_2_10
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (((a ^ (2 : ℕ)) + x) ≥ 0))
  (h3 : (forall (y : ℝ), (((y ∈ (Set.univ : Set ℝ)) ∧ (y ≥ 0))) → (((f : ℝ → _) y) = (Real.rpow y (((2 : ℝ))⁻¹)))))
  (h4 : y_0 = (a ^ (2 : ℕ)))
  (h5 : v_uCE_u94_y = x)
  (h6 : (y_0 + v_uCE_u94_y) = ((a ^ (2 : ℕ)) + x))
  (h7 : |((f (y_0 + v_uCE_u94_y)) - ((f y_0) + ((iteratedDeriv 1 (fun t => f t) y_0) * v_uCE_u94_y)))| ≤ (|(v_uCE_u94_y)| ^ (2 : ℕ)))
  (h8 : (iteratedDeriv 1 (fun t => f t) y_0) = (1 /. (2 * (Real.rpow y_0 (((2 : ℝ))⁻¹)))))
  (h9 : (Real.rpow y_0 (((2 : ℝ))⁻¹)) = a)
  (h10 : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)))
  (h11 : (Real.rpow (34 : ℝ) (((2 : ℝ))⁻¹)) = (Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)))
  (h12 : |((Real.rpow (((6 : ℕ) ^ (2 : ℕ)) - 2) (((2 : ℝ))⁻¹)) - (6 - (2 /. (2 * 6))))| ≤ (|((-(2 : ℤ)))| ^ (2 : ℕ)))
  (h13 : (6 - (2 /. (2 * 6))) = (((5833 : ℝ) /. (1000 : ℝ))))
  (h14 : (Real.rpow (34 : ℝ) (((2 : ℝ))⁻¹)) = (((5831 : ℝ) /. (1000 : ℝ))))
  : |((Real.rpow ((a ^ (2 : ℕ)) + x) (((2 : ℝ))⁻¹)) - (a + (x /. (2 * a))))| ≤ (|(x)| ^ (2 : ℕ)) := by
  sorry
