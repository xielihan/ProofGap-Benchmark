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

-- exercise: exercise_2802_1

theorem proof_gap_exercise_2802_1_1
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (v_uCE_uB1 ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((f (n, x)) = 0))))) := by
  sorry

theorem proof_gap_exercise_2802_1_2
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (v_uCE_uB1 ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((f (n, x)) = 0))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 0)))))) := by
  sorry

theorem proof_gap_exercise_2802_1_3
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (v_uCE_uB1 ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((f (n, x)) = 0))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 0)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ∈ (Set.Ioc 0 1))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (((Real.rpow n v_uCE_uB1_1) * x) * (Real.exp ((-n) * x)))) atTop (𝓝 0)))))) := by
  sorry

theorem proof_gap_exercise_2802_1_4
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (v_uCE_uB1 ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((f (n, x)) = 0))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 0)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ∈ (Set.Ioc 0 1))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (((Real.rpow n v_uCE_uB1_1) * x) * (Real.exp ((-n) * x)))) atTop (𝓝 0)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ∈ (Set.Ioc 0 1))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 0)))))) := by
  sorry

theorem proof_gap_exercise_2802_1_5
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (v_uCE_uB1 ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((f (n, x)) = 0))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 0)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ∈ (Set.Ioc 0 1))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (((Real.rpow n v_uCE_uB1_1) * x) * (Real.exp ((-n) * x)))) atTop (𝓝 0)))))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ∈ (Set.Ioc 0 1))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 0)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) → (∃ l, Filter.Tendsto (fun (n : ℕ) => (f (n, x))) Filter.atTop (𝓝 l)))) := by
  sorry

theorem proof_gap_exercise_2802_1_6
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (v_uCE_uB1 ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((f (n, x)) = 0))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 0)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ∈ (Set.Ioc 0 1))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (((Real.rpow n v_uCE_uB1_1) * x) * (Real.exp ((-n) * x)))) atTop (𝓝 0)))))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (x ∈ (Set.Ioc 0 1))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 0)))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Icc 0 1))) → (∃ l, Filter.Tendsto (fun (n : ℕ) => (f (n, x))) Filter.atTop (𝓝 l)))))
  : (v_uCE_uB1 ∈ (Set.univ : Set ℝ)) ↔ (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → (∃ l, Filter.Tendsto (fun (n : ℕ) => (f (n, x))) Filter.atTop (𝓝 l)))) := by
  sorry
