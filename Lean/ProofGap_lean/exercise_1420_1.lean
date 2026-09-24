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

-- exercise: exercise_1420_1

theorem proof_gap_exercise_1420_1_1
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : Even n)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))) := by
  sorry

theorem proof_gap_exercise_1420_1_2
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : Even n)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))) := by
  sorry

theorem proof_gap_exercise_1420_1_3
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : Even n)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1420_1_4
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : Even n)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : Not (0 ∈ (lpMaximumPoints y)) := by
  sorry

theorem proof_gap_exercise_1420_1_5
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : Even n)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h8 : Not (0 ∈ (lpMaximumPoints y)))
  : Not (0 ∈ (lpMinimumPoints y)) := by
  sorry

theorem proof_gap_exercise_1420_1_6
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : Even n)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h8 : Not (0 ∈ (lpMaximumPoints y)))
  (h9 : Not (0 ∈ (lpMinimumPoints y)))
  : (lpMaximumPoints y) = ∅ := by
  sorry

theorem proof_gap_exercise_1420_1_7
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (k : ℕ)
  (h1 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : k ∈ (Set.univ : Set ℕ))
  (h3 : Even n)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h8 : Not (0 ∈ (lpMaximumPoints y)))
  (h9 : Not (0 ∈ (lpMinimumPoints y)))
  (h10 : (lpMaximumPoints y) = ∅)
  : (lpMinimumPoints y) = ∅ := by
  sorry
