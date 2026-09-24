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

-- exercise: exercise_2617

theorem proof_gap_exercise_2617_1
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) > 0))) := by
  sorry

theorem proof_gap_exercise_2617_2
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) > 0))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → (((Real.log (1 /. (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))))) /. (Real.log (n : ℝ))) = (Real.log (Real.log (Real.log (n : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2617_3
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) > 0))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → (((Real.log (1 /. (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))))) /. (Real.log (n : ℝ))) = (Real.log (Real.log (Real.log (n : ℝ))))))))
  : (forall (v_uCE_uB1 : ℝ), (((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 > 0)) → (exists (n_0 : ℕ), ((((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n_0 ≥ 3)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.log (Real.log (Real.log (n : ℝ)))) ≥ (1 + v_uCE_uB1)))))))) := by
  sorry

theorem proof_gap_exercise_2617_4
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) > 0))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → (((Real.log (1 /. (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))))) /. (Real.log (n : ℝ))) = (Real.log (Real.log (Real.log (n : ℝ))))))))
  (h3 : (forall (v_uCE_uB1 : ℝ), (((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 > 0)) → (exists (n_0 : ℕ), ((((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n_0 ≥ 3)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.log (Real.log (Real.log (n : ℝ)))) ≥ (1 + v_uCE_uB1)))))))))
  : (forall (v_uCE_uB1 : ℝ), (((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 > 0)) → (exists (n_0 : ℕ), ((((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n_0 ≥ 3)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → (((Real.log (1 /. (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))))) /. (Real.log (n : ℝ))) ≥ (1 + v_uCE_uB1)))))))) := by
  sorry

theorem proof_gap_exercise_2617_5
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) > 0))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → (((Real.log (1 /. (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))))) /. (Real.log (n : ℝ))) = (Real.log (Real.log (Real.log (n : ℝ))))))))
  (h3 : (forall (v_uCE_uB1 : ℝ), (((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 > 0)) → (exists (n_0 : ℕ), ((((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n_0 ≥ 3)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.log (Real.log (Real.log (n : ℝ)))) ≥ (1 + v_uCE_uB1)))))))))
  (h4 : (forall (v_uCE_uB1 : ℝ), (((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 > 0)) → (exists (n_0 : ℕ), ((((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n_0 ≥ 3)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → (((Real.log (1 /. (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))))) /. (Real.log (n : ℝ))) ≥ (1 + v_uCE_uB1)))))))))
  : Summable (fun (n : ℕ) => if (3 : ℕ) ≤ n then (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) else 0) := by
  sorry

theorem proof_gap_exercise_2617_6
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → ((1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) > 0))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 3)) → (((Real.log (1 /. (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))))) /. (Real.log (n : ℝ))) = (Real.log (Real.log (Real.log (n : ℝ))))))))
  (h3 : (forall (v_uCE_uB1 : ℝ), (((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 > 0)) → (exists (n_0 : ℕ), ((((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n_0 ≥ 3)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → ((Real.log (Real.log (Real.log (n : ℝ)))) ≥ (1 + v_uCE_uB1)))))))))
  (h4 : (forall (v_uCE_uB1 : ℝ), (((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 > 0)) → (exists (n_0 : ℕ), ((((n_0 ∈ (Set.univ : Set ℕ)) ∧ (n_0 ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n_0 ≥ 3)) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ n_0)) → (((Real.log (1 /. (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))))) /. (Real.log (n : ℝ))) ≥ (1 + v_uCE_uB1)))))))))
  (h5 : Summable (fun (n : ℕ) => if (3 : ℕ) ≤ n then (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) else 0))
  : Summable (fun (n : ℕ) => if (3 : ℕ) ≤ n then (1 /. (Real.rpow (Real.log (Real.log (n : ℝ))) (Real.log (n : ℝ)))) else 0) := by
  sorry
