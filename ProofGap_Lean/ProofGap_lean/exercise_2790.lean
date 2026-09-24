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

-- exercise: exercise_2790

theorem proof_gap_exercise_2790_1
  (a : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → (0 < (1 /. (Real.rpow (n_1 : ℝ) x))))))) := by
  sorry

theorem proof_gap_exercise_2790_2
  (a : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → (0 < (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((1 /. (Real.rpow (n_1 : ℝ) x)) ≤ 1))))) := by
  sorry

theorem proof_gap_exercise_2790_3
  (a : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → (0 < (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  (h6 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((1 /. (Real.rpow (n_1 : ℝ) x)) ≤ 1))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x)))))) := by
  sorry

theorem proof_gap_exercise_2790_4
  (a : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → (0 < (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  (h6 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((1 /. (Real.rpow (n_1 : ℝ) x)) ≤ 1))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Bornology.IsBounded (Set.range (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x))))))) := by
  sorry

theorem proof_gap_exercise_2790_5
  (a : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → (0 < (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  (h6 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((1 /. (Real.rpow (n_1 : ℝ) x)) ≤ 1))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Bornology.IsBounded (Set.range (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ), ((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (a k_1)))| < v_uCE_uB5))))))) := by
  sorry

theorem proof_gap_exercise_2790_6
  (a : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → (0 < (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  (h6 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((1 /. (Real.rpow (n_1 : ℝ) x)) ≤ 1))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Bornology.IsBounded (Set.range (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  (h9 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ), ((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (a k_1)))| < v_uCE_uB5))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), ((a k_1) /. (Real.rpow (k_1 : ℝ) x))))| < v_uCE_uB5))))))) := by
  sorry

theorem proof_gap_exercise_2790_7
  (a : (ℕ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : k ∈ (Set.univ : Set ℕ))
  (h4 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → (0 < (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  (h6 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((1 /. (Real.rpow (n_1 : ℝ) x)) ≤ 1))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x)))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Bornology.IsBounded (Set.range (fun (n_1 : ℕ) => (1 /. (Real.rpow (n_1 : ℝ) x))))))))
  (h9 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ), ((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (a k_1)))| < v_uCE_uB5))))))))
  (h10 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), ((a k_1) /. (Real.rpow (k_1 : ℝ) x))))| < v_uCE_uB5))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), ((a k_1) /. (Real.rpow (k_1 : ℝ) x))))| < v_uCE_uB5))))))) := by
  sorry
