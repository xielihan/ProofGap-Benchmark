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

-- exercise: exercise_1420_2

theorem proof_gap_exercise_1420_2_1
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : Odd n)
  (h4 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))) := by
  sorry

theorem proof_gap_exercise_1420_2_2
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : Odd n)
  (h4 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))) := by
  sorry

theorem proof_gap_exercise_1420_2_3
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : Odd n)
  (h4 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1420_2_4
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : Odd n)
  (h4 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1420_2_5
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : Odd n)
  (h4 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (lpMaximumPoints y) = ({x | x = 0}) := by
  sorry

theorem proof_gap_exercise_1420_2_6
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : Odd n)
  (h4 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h9 : (lpMaximumPoints y) = ({x | x = 0}))
  : (y (0 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_1420_2_7
  (y : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : Odd n)
  (h4 : (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((∑ k_1 ∈ Finset.Icc (0 : ℕ) n, ((x ^ k_1) /. (k_1)!)) * (Real.exp (-x)))))))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((-(1 /. (n)!)) * (Real.exp (-x))) * (x ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => y t) x) = 0) ↔ (x = 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h9 : (lpMaximumPoints y) = ({x | x = 0}))
  (h10 : (y (0 : ℝ)) = 1)
  : (lpMinimumPoints y) = ∅ := by
  sorry
