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

-- exercise: exercise_2630

theorem proof_gap_exercise_2630_1
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))) := by
  sorry

theorem proof_gap_exercise_2630_2
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))) := by
  sorry

theorem proof_gap_exercise_2630_3
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)) := by
  sorry

theorem proof_gap_exercise_2630_4
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)) := by
  sorry

theorem proof_gap_exercise_2630_5
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)) := by
  sorry

theorem proof_gap_exercise_2630_6
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)) := by
  sorry

theorem proof_gap_exercise_2630_7
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h9 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)))
  : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)) := by
  sorry

theorem proof_gap_exercise_2630_8
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h9 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)))
  (h10 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2630_9
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h9 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)))
  (h10 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h11 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  : (a ≤ 2) → (Tendsto (fun n : ℝ => ((Real.log n) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_2630_10
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h9 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)))
  (h10 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h11 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h12 : (a ≤ 2) → (Tendsto (fun n : ℝ => ((Real.log n) : EReal)) atTop (𝓝 ⊤)))
  : (a ≤ 2) → (Tendsto (fun n : ℕ => (((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.log (k : ℝ))) /. n) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_2630_11
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h9 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)))
  (h10 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h11 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h12 : (a ≤ 2) → (Tendsto (fun n : ℝ => ((Real.log n) : EReal)) atTop (𝓝 ⊤)))
  (h13 : (a ≤ 2) → (Tendsto (fun n : ℕ => (((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.log (k : ℝ))) /. n) : EReal)) atTop (𝓝 ⊤)))
  : (a ≤ 2) → (Tendsto (fun n : ℕ => (((u n) /. (1 /. (Real.rpow (n : ℝ) (a - 1)))) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_2630_12
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h9 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)))
  (h10 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h11 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h12 : (a ≤ 2) → (Tendsto (fun n : ℝ => ((Real.log n) : EReal)) atTop (𝓝 ⊤)))
  (h13 : (a ≤ 2) → (Tendsto (fun n : ℕ => (((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.log (k : ℝ))) /. n) : EReal)) atTop (𝓝 ⊤)))
  (h14 : (a ≤ 2) → (Tendsto (fun n : ℕ => (((u n) /. (1 /. (Real.rpow (n : ℝ) (a - 1)))) : EReal)) atTop (𝓝 ⊤)))
  : (a ≤ 2) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)) := by
  sorry

theorem proof_gap_exercise_2630_13
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h9 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)))
  (h10 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h11 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h12 : (a ≤ 2) → (Tendsto (fun n : ℝ => ((Real.log n) : EReal)) atTop (𝓝 ⊤)))
  (h13 : (a ≤ 2) → (Tendsto (fun n : ℕ => (((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.log (k : ℝ))) /. n) : EReal)) atTop (𝓝 ⊤)))
  (h14 : (a ≤ 2) → (Tendsto (fun n : ℕ => (((u n) /. (1 /. (Real.rpow (n : ℝ) (a - 1)))) : EReal)) atTop (𝓝 ⊤)))
  (h15 : (a ≤ 2) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  : (a ≤ 2) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2630_14
  (u : (ℕ -> ℝ))
  (v_uCE_uB8 : (ℕ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((Real.log ((n)! : ℝ)) /. (Real.rpow (n : ℝ) a))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((0 < (v_uCE_uB8 n)) ∧ ((v_uCE_uB8 n) < 1)))))
  (h4 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((n)! = (((Real.rpow ((2 * Real.pi) * n) (((2 : ℝ))⁻¹)) * (n ^ n)) * (Real.exp ((-(n : ℝ)) + ((v_uCE_uB8 n) /. (12 * n)))))))))
  (h5 : (a > 2) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = ((((((Real.log (2 * Real.pi)) /. (2 * (Real.rpow (n : ℝ) a))) + ((Real.log (n : ℝ)) /. (2 * (Real.rpow (n : ℝ) a)))) + ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1)))) + ((v_uCE_uB8 n) /. (12 * (Real.rpow (n : ℝ) (a + 1))))) - (1 /. (Real.rpow (n : ℝ) (a - 1))))))))
  (h6 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) a)) else 0)))
  (h7 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) a)) else 0)))
  (h8 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((Real.log (n : ℝ)) /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h9 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB8 n) /. (Real.rpow (n : ℝ) (a + 1))) else 0)))
  (h10 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h11 : (a > 2) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h12 : (a ≤ 2) → (Tendsto (fun n : ℝ => ((Real.log n) : EReal)) atTop (𝓝 ⊤)))
  (h13 : (a ≤ 2) → (Tendsto (fun n : ℕ => (((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.log (k : ℝ))) /. n) : EReal)) atTop (𝓝 ⊤)))
  (h14 : (a ≤ 2) → (Tendsto (fun n : ℕ => (((u n) /. (1 /. (Real.rpow (n : ℝ) (a - 1)))) : EReal)) atTop (𝓝 ⊤)))
  (h15 : (a ≤ 2) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (n : ℝ) (a - 1))) else 0)))
  (h16 : (a ≤ 2) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  : (a ∈ ({a_1 | (a_1 ∈ (Set.univ : Set ℝ)) ∧ (a_1 > 2)})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry
