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

-- exercise: exercise_2797

theorem proof_gap_exercise_2797_1
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2797_2
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  : ContinuousOn v_uCE_uB6 (Set.Ioi 1) := by
  sorry

theorem proof_gap_exercise_2797_3
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))) := by
  sorry

theorem proof_gap_exercise_2797_4
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))) := by
  sorry

theorem proof_gap_exercise_2797_5
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))) := by
  sorry

theorem proof_gap_exercise_2797_6
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))) := by
  sorry

theorem proof_gap_exercise_2797_7
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2797_8
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))) := by
  sorry

theorem proof_gap_exercise_2797_9
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))) := by
  sorry

theorem proof_gap_exercise_2797_10
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))) := by
  sorry

theorem proof_gap_exercise_2797_11
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  (h11 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ici a)))) := by
  sorry

theorem proof_gap_exercise_2797_12
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  (h11 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h12 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ici a)))))
  : ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1) := by
  sorry

theorem proof_gap_exercise_2797_13
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  (h11 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h12 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ici a)))))
  (h13 : ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) a)) else 0)))))) := by
  sorry

theorem proof_gap_exercise_2797_14
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  (h11 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h12 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ici a)))))
  (h13 : ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1))
  (h14 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) a)) else 0)))))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))) := by
  sorry

theorem proof_gap_exercise_2797_15
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  (h11 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h12 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ici a)))))
  (h13 : ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1))
  (h14 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) a)) else 0)))))))
  (h15 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv k (fun t => v_uCE_uB6 t) x) = (((-(1 : ℤ)) ^ k) * (∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0))))))) := by
  sorry

theorem proof_gap_exercise_2797_16
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  (h11 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h12 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ici a)))))
  (h13 : ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1))
  (h14 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) a)) else 0)))))))
  (h15 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))))
  (h16 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv k (fun t => v_uCE_uB6 t) x) = (((-(1 : ℤ)) ^ k) * (∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv k (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1)))) := by
  sorry

theorem proof_gap_exercise_2797_17
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  (h11 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h12 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ici a)))))
  (h13 : ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1))
  (h14 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) a)) else 0)))))))
  (h15 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))))
  (h16 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv k (fun t => v_uCE_uB6 t) x) = (((-(1 : ℤ)) ^ k) * (∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h17 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv k (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1)))))
  : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContDiffOn ℝ (k : ℕ∞) v_uCE_uB6 (Set.Ioi 1)))) := by
  sorry

theorem proof_gap_exercise_2797_18
  (v_uCE_uB6 : (ℝ -> ℝ))
  (h1 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((v_uCE_uB6 x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (1 /. (Real.rpow (n_1 : ℝ) x)) else 0)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h3 : ContinuousOn v_uCE_uB6 (Set.Ioi 1))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))
  (h5 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))))))))))
  (h6 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) ≤ ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h7 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) ∧ ((x : EReal) < ⊤)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a))))))))))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))))
  (h9 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))
  (h10 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x_1 : ℝ) => ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x_1))) (Set.Ici a)))))))
  (h11 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → ((iteratedDeriv 1 (fun t => v_uCE_uB6 t) x) = (-(∑' n, if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h12 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ici a)))))
  (h13 : ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv 1 (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1))
  (h14 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) a)) else 0)))))))
  (h15 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a > 1)) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (a ≤ x)) → (TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x))) (fun x => ∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0) Filter.atTop (Set.Ici a)))))))))
  (h16 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((iteratedDeriv k (fun t => v_uCE_uB6 t) x) = (((-(1 : ℤ)) ^ k) * (∑' n, if (1 : ℕ) ≤ n then (((Real.log (n : ℝ)) ^ k) /. (Real.rpow (n : ℝ) x)) else 0))))))))
  (h17 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContinuousOn (fun (x1 : ℝ) => (iteratedDeriv k (fun t => v_uCE_uB6 t) x1)) (Set.Ioi 1)))))
  (h18 : (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContDiffOn ℝ (k : ℕ∞) v_uCE_uB6 (Set.Ioi 1)))))
  : (ContinuousOn v_uCE_uB6 (Set.Ioi 1)) ∧ (forall (k : ℕ), (((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) → (ContDiffOn ℝ (k : ℕ∞) v_uCE_uB6 (Set.Ioi 1)))) := by
  sorry
