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

-- exercise: exercise_2368

theorem proof_gap_exercise_2368_1
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((((Real.sin x) ^ (2 : ℕ)) /. x) = ((1 - (Real.cos (2 * x))) /. (2 * x))) ∧ (((1 - (Real.cos (2 * x))) /. (2 * x)) = ((1 /. 2) * ((1 /. x) - ((Real.cos (2 * x)) /. x))))))) := by
  sorry

theorem proof_gap_exercise_2368_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((((Real.sin x) ^ (2 : ℕ)) /. x) = ((1 - (Real.cos (2 * x))) /. (2 * x))) ∧ (((1 - (Real.cos (2 * x))) /. (2 * x)) = ((1 /. 2) * ((1 /. x) - ((Real.cos (2 * x)) /. x))))))))
  : Not ((∫ x in Set.Ioi (1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_2368_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((((Real.sin x) ^ (2 : ℕ)) /. x) = ((1 - (Real.cos (2 * x))) /. (2 * x))) ∧ (((1 - (Real.cos (2 * x))) /. (2 * x)) = ((1 /. 2) * ((1 /. x) - ((Real.cos (2 * x)) /. x))))))))
  (h2 : Not ((∫ x in Set.Ioi (1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  : (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > 1)) → (|((∫ x in (1 : ℝ)..A, ((Real.cos (2 * x)) * (1 : ℝ))))| ≤ 2))) := by
  sorry

theorem proof_gap_exercise_2368_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((((Real.sin x) ^ (2 : ℕ)) /. x) = ((1 - (Real.cos (2 * x))) /. (2 * x))) ∧ (((1 - (Real.cos (2 * x))) /. (2 * x)) = ((1 /. 2) * ((1 /. x) - ((Real.cos (2 * x)) /. x))))))))
  (h2 : Not ((∫ x in Set.Ioi (1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h3 : (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > 1)) → (|((∫ x in (1 : ℝ)..A, ((Real.cos (2 * x)) * (1 : ℝ))))| ≤ 2))))
  : Tendsto (fun x : ℝ => (1 /. x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2368_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((((Real.sin x) ^ (2 : ℕ)) /. x) = ((1 - (Real.cos (2 * x))) /. (2 * x))) ∧ (((1 - (Real.cos (2 * x))) /. (2 * x)) = ((1 /. 2) * ((1 /. x) - ((Real.cos (2 * x)) /. x))))))))
  (h2 : Not ((∫ x in Set.Ioi (1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h3 : (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > 1)) → (|((∫ x in (1 : ℝ)..A, ((Real.cos (2 * x)) * (1 : ℝ))))| ≤ 2))))
  (h4 : Tendsto (fun x : ℝ => (1 /. x)) atTop (𝓝 0))
  : (∫ x in Set.Ioi (1 : ℝ), (((Real.cos (2 * x)) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ) := by
  sorry

theorem proof_gap_exercise_2368_6
  (DefInt_1_PosInfty_Mult_fun_x_And_Belong_x_RealSet_Gt_x_1_frac_cos_Mult_2_x_x_diff_fun_x_And_Belong_x_RealSet_Gt_x_1_x : ℝ)
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((((Real.sin x) ^ (2 : ℕ)) /. x) = ((1 - (Real.cos (2 * x))) /. (2 * x))) ∧ (((1 - (Real.cos (2 * x))) /. (2 * x)) = ((1 /. 2) * ((1 /. x) - ((Real.cos (2 * x)) /. x))))))))
  (h2 : Not ((∫ x in Set.Ioi (1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h3 : (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > 1)) → (|((∫ x in (1 : ℝ)..A, ((Real.cos (2 * x)) * (1 : ℝ))))| ≤ 2))))
  (h4 : Tendsto (fun x : ℝ => (1 /. x)) atTop (𝓝 0))
  (h5 : DefInt_1_PosInfty_Mult_fun_x_And_Belong_x_RealSet_Gt_x_1_frac_cos_Mult_2_x_x_diff_fun_x_And_Belong_x_RealSet_Gt_x_1_x ∈ (Set.univ : Set ℝ))
  : Not ((∫ x in Set.Ioi (1 : ℝ), ((((Real.sin x) ^ (2 : ℕ)) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_2368_7
  (DefInt_1_PosInfty_Mult_fun_x_And_Belong_x_RealSet_Gt_x_1_frac_cos_Mult_2_x_x_diff_fun_x_And_Belong_x_RealSet_Gt_x_1_x : ℝ)
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((((Real.sin x) ^ (2 : ℕ)) /. x) = ((1 - (Real.cos (2 * x))) /. (2 * x))) ∧ (((1 - (Real.cos (2 * x))) /. (2 * x)) = ((1 /. 2) * ((1 /. x) - ((Real.cos (2 * x)) /. x))))))))
  (h2 : Not ((∫ x in Set.Ioi (1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h3 : (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > 1)) → (|((∫ x in (1 : ℝ)..A, ((Real.cos (2 * x)) * (1 : ℝ))))| ≤ 2))))
  (h4 : Tendsto (fun x : ℝ => (1 /. x)) atTop (𝓝 0))
  (h5 : DefInt_1_PosInfty_Mult_fun_x_And_Belong_x_RealSet_Gt_x_1_frac_cos_Mult_2_x_x_diff_fun_x_And_Belong_x_RealSet_Gt_x_1_x ∈ (Set.univ : Set ℝ))
  (h6 : Not ((∫ x in Set.Ioi (1 : ℝ), ((((Real.sin x) ^ (2 : ℕ)) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  : Not ((∫ x in Set.Ioi (0 : ℝ), ((((Real.sin x) ^ (2 : ℕ)) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) := by
  sorry

theorem proof_gap_exercise_2368_8
  (DefInt_1_PosInfty_Mult_fun_x_And_Belong_x_RealSet_Gt_x_1_frac_cos_Mult_2_x_x_diff_fun_x_And_Belong_x_RealSet_Gt_x_1_x : ℝ)
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((((Real.sin x) ^ (2 : ℕ)) /. x) = ((1 - (Real.cos (2 * x))) /. (2 * x))) ∧ (((1 - (Real.cos (2 * x))) /. (2 * x)) = ((1 /. 2) * ((1 /. x) - ((Real.cos (2 * x)) /. x))))))))
  (h2 : Not ((∫ x in Set.Ioi (1 : ℝ), (((1 : ℝ) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h3 : (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > 1)) → (|((∫ x in (1 : ℝ)..A, ((Real.cos (2 * x)) * (1 : ℝ))))| ≤ 2))))
  (h4 : Tendsto (fun x : ℝ => (1 /. x)) atTop (𝓝 0))
  (h5 : DefInt_1_PosInfty_Mult_fun_x_And_Belong_x_RealSet_Gt_x_1_frac_cos_Mult_2_x_x_diff_fun_x_And_Belong_x_RealSet_Gt_x_1_x ∈ (Set.univ : Set ℝ))
  (h6 : Not ((∫ x in Set.Ioi (1 : ℝ), ((((Real.sin x) ^ (2 : ℕ)) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  (h7 : Not ((∫ x in Set.Ioi (0 : ℝ), ((((Real.sin x) ^ (2 : ℕ)) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)))
  : Not ((∫ x in Set.Ioi (0 : ℝ), ((((Real.sin x) ^ (2 : ℕ)) /. x) * (1 : ℝ))) ∈ (Set.univ : Set ℝ)) := by
  sorry
