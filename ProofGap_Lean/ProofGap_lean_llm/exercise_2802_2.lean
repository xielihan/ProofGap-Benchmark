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

-- exercise: exercise_2802_2

theorem proof_gap_exercise_2802_2_1
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))) := by
  sorry

theorem proof_gap_exercise_2802_2_2
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))) := by
  sorry

theorem proof_gap_exercise_2802_2_3
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))) := by
  sorry

theorem proof_gap_exercise_2802_2_4
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))) := by
  sorry

theorem proof_gap_exercise_2802_2_5
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  (h6 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((lpMaximumPointsOn (fun (x : ℝ) => (f (n, x))) (Set.Icc 0 1)) = ({x | x = (1 /. n)})))) := by
  sorry

theorem proof_gap_exercise_2802_2_6
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  (h6 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((lpMaximumPointsOn (fun (x : ℝ) => (f (n, x))) (Set.Icc 0 1)) = ({x | x = (1 /. n)})))))
  : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (((0 ≤ (f (n, x))) ∧ ((f (n, x)) ≤ (f (n, (1 /. n))))) ∧ ((f (n, (1 /. n))) = ((Real.rpow (n : ℝ) (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ)))))))) := by
  sorry

theorem proof_gap_exercise_2802_2_7
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  (h6 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((lpMaximumPointsOn (fun (x : ℝ) => (f (n, x))) (Set.Icc 0 1)) = ({x | x = (1 /. n)})))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (((0 ≤ (f (n, x))) ∧ ((f (n, x)) ≤ (f (n, (1 /. n))))) ∧ ((f (n, (1 /. n))) = ((Real.rpow (n : ℝ) (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ)))))))))
  : (v_uCE_uB1 < 1) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0)) := by
  sorry

theorem proof_gap_exercise_2802_2_8
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  (h6 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((lpMaximumPointsOn (fun (x : ℝ) => (f (n, x))) (Set.Icc 0 1)) = ({x | x = (1 /. n)})))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (((0 ≤ (f (n, x))) ∧ ((f (n, x)) ≤ (f (n, (1 /. n))))) ∧ ((f (n, (1 /. n))) = ((Real.rpow (n : ℝ) (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ)))))))))
  (h9 : (v_uCE_uB1 < 1) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0)))
  : (v_uCE_uB1 < 1) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n > N)) ∧ (x ∈ (Set.Icc 0 1))) → (|(((f (n, x)) - 0))| < v_uCE_uB5))))))) := by
  sorry

theorem proof_gap_exercise_2802_2_9
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  (h6 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((lpMaximumPointsOn (fun (x : ℝ) => (f (n, x))) (Set.Icc 0 1)) = ({x | x = (1 /. n)})))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (((0 ≤ (f (n, x))) ∧ ((f (n, x)) ≤ (f (n, (1 /. n))))) ∧ ((f (n, (1 /. n))) = ((Real.rpow (n : ℝ) (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ)))))))))
  (h9 : (v_uCE_uB1 < 1) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0)))
  (h10 : (v_uCE_uB1 < 1) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n > N)) ∧ (x ∈ (Set.Icc 0 1))) → (|(((f (n, x)) - 0))| < v_uCE_uB5))))))))
  : (v_uCE_uB1 < 1) → (TendstoUniformlyOn (fun n x => f (n, x)) (fun (x : ℝ) => 0) Filter.atTop (Set.Icc 0 1)) := by
  sorry

theorem proof_gap_exercise_2802_2_10
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  (h6 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((lpMaximumPointsOn (fun (x : ℝ) => (f (n, x))) (Set.Icc 0 1)) = ({x | x = (1 /. n)})))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (((0 ≤ (f (n, x))) ∧ ((f (n, x)) ≤ (f (n, (1 /. n))))) ∧ ((f (n, (1 /. n))) = ((Real.rpow (n : ℝ) (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ)))))))))
  (h9 : (v_uCE_uB1 < 1) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0)))
  (h10 : (v_uCE_uB1 < 1) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n > N)) ∧ (x ∈ (Set.Icc 0 1))) → (|(((f (n, x)) - 0))| < v_uCE_uB5))))))))
  (h11 : (v_uCE_uB1 < 1) → (TendstoUniformlyOn (fun n x => f (n, x)) (fun (x : ℝ) => 0) Filter.atTop (Set.Icc 0 1)))
  : (v_uCE_uB1 ≥ 1) → (Not (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0))) := by
  sorry

theorem proof_gap_exercise_2802_2_11
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  (h6 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((lpMaximumPointsOn (fun (x : ℝ) => (f (n, x))) (Set.Icc 0 1)) = ({x | x = (1 /. n)})))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (((0 ≤ (f (n, x))) ∧ ((f (n, x)) ≤ (f (n, (1 /. n))))) ∧ ((f (n, (1 /. n))) = ((Real.rpow (n : ℝ) (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ)))))))))
  (h9 : (v_uCE_uB1 < 1) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0)))
  (h10 : (v_uCE_uB1 < 1) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n > N)) ∧ (x ∈ (Set.Icc 0 1))) → (|(((f (n, x)) - 0))| < v_uCE_uB5))))))))
  (h11 : (v_uCE_uB1 < 1) → (TendstoUniformlyOn (fun n x => f (n, x)) (fun (x : ℝ) => 0) Filter.atTop (Set.Icc 0 1)))
  (h12 : (v_uCE_uB1 ≥ 1) → (Not (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0))))
  : (v_uCE_uB1 ≥ 1) → (Not (TendstoUniformlyOn (fun n x => f (n, x)) (fun (x : ℝ) => 0) Filter.atTop (Set.Icc 0 1))) := by
  sorry

theorem proof_gap_exercise_2802_2_12
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) = (((Real.rpow (n : ℝ) v_uCE_uB1) * (Real.exp ((-(n : ℝ)) * x))) * (1 - (n * x)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((iteratedDeriv 1 (fun t => f (n, t)) (1 /. n)) = 0))))
  (h5 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x < (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) > 0))))
  (h6 : (forall (n : ℕ) (x : ℝ), ((((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) ∧ (x > (1 /. n))) → ((iteratedDeriv 1 (fun t => f (n, t)) x) < 0))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((lpMaximumPointsOn (fun (x : ℝ) => (f (n, x))) (Set.Icc 0 1)) = ({x | x = (1 /. n)})))))
  (h8 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (((0 ≤ (f (n, x))) ∧ ((f (n, x)) ≤ (f (n, (1 /. n))))) ∧ ((f (n, (1 /. n))) = ((Real.rpow (n : ℝ) (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ)))))))))
  (h9 : (v_uCE_uB1 < 1) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0)))
  (h10 : (v_uCE_uB1 < 1) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n > N)) ∧ (x ∈ (Set.Icc 0 1))) → (|(((f (n, x)) - 0))| < v_uCE_uB5))))))))
  (h11 : (v_uCE_uB1 < 1) → (TendstoUniformlyOn (fun n x => f (n, x)) (fun (x : ℝ) => 0) Filter.atTop (Set.Icc 0 1)))
  (h12 : (v_uCE_uB1 ≥ 1) → (Not (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 1)) * (Real.exp (-(1 : ℝ))))) atTop (𝓝 0))))
  (h13 : (v_uCE_uB1 ≥ 1) → (Not (TendstoUniformlyOn (fun n x => f (n, x)) (fun (x : ℝ) => 0) Filter.atTop (Set.Icc 0 1))))
  : (v_uCE_uB1 ∈ ({v_uCE_uB1_1 | (v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 < 1)})) ↔ (TendstoUniformlyOn (fun n x => f (n, x)) (fun (x : ℝ) => 0) Filter.atTop (Set.Icc 0 1)) := by
  sorry
