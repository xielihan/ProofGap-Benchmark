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

-- exercise: exercise_1394_4

theorem proof_gap_exercise_1394_4_1
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)) := by
  sorry

theorem proof_gap_exercise_1394_4_2
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1394_4_3
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))) := by
  sorry

theorem proof_gap_exercise_1394_4_4
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  (h7 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))))
  : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1))) := by
  sorry

theorem proof_gap_exercise_1394_4_5
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  (h7 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))))
  (h8 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1))))
  : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| = ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|) := by
  sorry

theorem proof_gap_exercise_1394_4_6
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  (h7 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))))
  (h8 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1))))
  (h9 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| = ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|))
  : ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|) ≤ (3 /. 8) := by
  sorry

theorem proof_gap_exercise_1394_4_7
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  (h7 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))))
  (h8 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1))))
  (h9 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| = ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|))
  (h10 : ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|) ≤ (3 /. 8))
  : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| ≤ (3 /. 8) := by
  sorry

theorem proof_gap_exercise_1394_4_8
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  (h7 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))))
  (h8 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1))))
  (h9 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| = ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|))
  (h10 : ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|) ≤ (3 /. 8))
  (h11 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| ≤ (3 /. 8))
  : |((R_3 x))| ≤ ((3 /. 8) * (1 /. ((3 : ℕ))!)) := by
  sorry

theorem proof_gap_exercise_1394_4_9
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  (h7 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))))
  (h8 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1))))
  (h9 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| = ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|))
  (h10 : ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|) ≤ (3 /. 8))
  (h11 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| ≤ (3 /. 8))
  (h12 : |((R_3 x))| ≤ ((3 /. 8) * (1 /. ((3 : ℕ))!)))
  : ((3 /. 8) * (1 /. ((3 : ℕ))!)) = (1 /. 16) := by
  sorry

theorem proof_gap_exercise_1394_4_10
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  (h7 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))))
  (h8 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1))))
  (h9 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| = ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|))
  (h10 : ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|) ≤ (3 /. 8))
  (h11 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| ≤ (3 /. 8))
  (h12 : |((R_3 x))| ≤ ((3 /. 8) * (1 /. ((3 : ℕ))!)))
  (h13 : ((3 /. 8) * (1 /. ((3 : ℕ))!)) = (1 /. 16))
  : |((R_3 x))| ≤ (1 /. 16) := by
  sorry

theorem proof_gap_exercise_1394_4_11
  (R_3 : (ℝ -> ℝ))
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : 0 ≤ x)
  (h3 : x ≤ 1)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ (-(1 : ℝ))))) → (((f : ℝ → _) t) = (Real.rpow (1 + t) (((2 : ℝ))⁻¹)))))
  (h5 : (Real.rpow (1 + x) (((2 : ℝ))⁻¹)) = (((1 + (x /. 2)) - ((x ^ (2 : ℕ)) /. 8)) + (R_3 x)))
  (h6 : (exists (v_uCE_uB8 : ℝ), ((((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1)) ∧ ((R_3 x) = (((iteratedDeriv 3 (fun t_1 => f t_1) (v_uCE_uB8 * x)) /. ((3 : ℕ))!) * (x ^ (3 : ℕ)))))))
  (h7 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB8 < 1)) ∧ (0 < v_uCE_uB8))))
  (h8 : (exists (v_uCE_uB8 : ℝ), (((v_uCE_uB8 ∈ (Set.univ : Set ℝ)) ∧ (0 < v_uCE_uB8)) ∧ (v_uCE_uB8 < 1))))
  (h9 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| = ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|))
  (h10 : ((3 /. 8) * |((1 /. (Real.rpow (1 + x) (5 /. 2))))|) ≤ (3 /. 8))
  (h11 : |((iteratedDeriv 3 (fun t_1 => f t_1) x))| ≤ (3 /. 8))
  (h12 : |((R_3 x))| ≤ ((3 /. 8) * (1 /. ((3 : ℕ))!)))
  (h13 : ((3 /. 8) * (1 /. ((3 : ℕ))!)) = (1 /. 16))
  (h14 : |((R_3 x))| ≤ (1 /. 16))
  : |((R_3 x))| ≤ (1 /. 16) := by
  sorry
