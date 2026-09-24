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

-- exercise: exercise_3070

theorem proof_gap_exercise_3070_1
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (((n ^ (2 : ℕ)) - 1) /. ((n ^ (2 : ℕ)) + 1)) p)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℕ) n, (a i_1))))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)))) := by
  sorry

theorem proof_gap_exercise_3070_2
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (((n ^ (2 : ℕ)) - 1) /. ((n ^ (2 : ℕ)) + 1)) p)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℕ) n, (a i_1))))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((1 - (2 /. ((n ^ (2 : ℕ)) + 1))) > 0))) := by
  sorry

theorem proof_gap_exercise_3070_3
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (((n ^ (2 : ℕ)) - 1) /. ((n ^ (2 : ℕ)) + 1)) p)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℕ) n, (a i_1))))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((1 - (2 /. ((n ^ (2 : ℕ)) + 1))) > 0))))
  : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (2 /. ((n ^ (2 : ℕ)) + 1)) else 0) := by
  sorry

theorem proof_gap_exercise_3070_4
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (((n ^ (2 : ℕ)) - 1) /. ((n ^ (2 : ℕ)) + 1)) p)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℕ) n, (a i_1))))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((1 - (2 /. ((n ^ (2 : ℕ)) + 1))) > 0))))
  (h6 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (2 /. ((n ^ (2 : ℕ)) + 1)) else 0))
  : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (Real.log (1 - (2 /. ((n ^ (2 : ℕ)) + 1)))) else 0) := by
  sorry

theorem proof_gap_exercise_3070_5
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (((n ^ (2 : ℕ)) - 1) /. ((n ^ (2 : ℕ)) + 1)) p)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℕ) n, (a i_1))))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((1 - (2 /. ((n ^ (2 : ℕ)) + 1))) > 0))))
  (h6 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (2 /. ((n ^ (2 : ℕ)) + 1)) else 0))
  (h7 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (Real.log (1 - (2 /. ((n ^ (2 : ℕ)) + 1)))) else 0))
  : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (Real.log (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)) else 0) := by
  sorry

theorem proof_gap_exercise_3070_6
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (((n ^ (2 : ℕ)) - 1) /. ((n ^ (2 : ℕ)) + 1)) p)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℕ) n, (a i_1))))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((1 - (2 /. ((n ^ (2 : ℕ)) + 1))) > 0))))
  (h6 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (2 /. ((n ^ (2 : ℕ)) + 1)) else 0))
  (h7 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (Real.log (1 - (2 /. ((n ^ (2 : ℕ)) + 1)))) else 0))
  (h8 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (Real.log (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)) else 0))
  : (exists (L : ℝ), (((L ∈ (Set.univ : Set ℝ)) ∧ (L ≠ 0)) ∧ (Tendsto (fun n : ℕ => (P n)) atTop (𝓝 L)))) := by
  sorry

theorem proof_gap_exercise_3070_7
  (a : (ℕ -> ℝ))
  (P : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (((n ^ (2 : ℕ)) - 1) /. ((n ^ (2 : ℕ)) + 1)) p)))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → ((P n) = (∏ i_1 ∈ Finset.Icc (2 : ℕ) n, (a i_1))))))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)))))
  (h5 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((1 - (2 /. ((n ^ (2 : ℕ)) + 1))) > 0))))
  (h6 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (2 /. ((n ^ (2 : ℕ)) + 1)) else 0))
  (h7 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (Real.log (1 - (2 /. ((n ^ (2 : ℕ)) + 1)))) else 0))
  (h8 : Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (Real.log (Real.rpow (1 - (2 /. ((n ^ (2 : ℕ)) + 1))) p)) else 0))
  (h9 : (exists (L : ℝ), (((L ∈ (Set.univ : Set ℝ)) ∧ (L ≠ 0)) ∧ (Tendsto (fun n : ℕ => (P n)) atTop (𝓝 L)))))
  : (exists (L : ℝ), (((L ∈ (Set.univ : Set ℝ)) ∧ (L ≠ 0)) ∧ (Tendsto (fun n : ℕ => (P n)) atTop (𝓝 L)))) := by
  sorry
