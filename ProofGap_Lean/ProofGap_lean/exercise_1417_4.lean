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

-- exercise: exercise_1417_4

theorem proof_gap_exercise_1417_4_1
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (x : ℝ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ m) * ((1 - x_1) ^ n))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((x_1 ^ (m - 1)) * ((1 - x_1) ^ (n - 1))) * (m - ((m + n) * x_1)))))) := by
  sorry

theorem proof_gap_exercise_1417_4_2
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (x : ℝ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ m) * ((1 - x_1) ^ n))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((x_1 ^ (m - 1)) * ((1 - x_1) ^ (n - 1))) * (m - ((m + n) * x_1)))))))
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x_1) = 0)) → (((x_1 = 0) ∨ (x_1 = 1)) ∨ (x_1 = (m /. (m + n)))))) := by
  sorry

theorem proof_gap_exercise_1417_4_3
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (x : ℝ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ m) * ((1 - x_1) ^ n))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((x_1 ^ (m - 1)) * ((1 - x_1) ^ (n - 1))) * (m - ((m + n) * x_1)))))))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x_1) = 0)) → (((x_1 = 0) ∨ (x_1 = 1)) ∨ (x_1 = (m /. (m + n)))))))
  : (Even n) → (1 ∈ (lpMinimumPoints y)) := by
  sorry

theorem proof_gap_exercise_1417_4_4
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (x : ℝ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ m) * ((1 - x_1) ^ n))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((x_1 ^ (m - 1)) * ((1 - x_1) ^ (n - 1))) * (m - ((m + n) * x_1)))))))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x_1) = 0)) → (((x_1 = 0) ∨ (x_1 = 1)) ∨ (x_1 = (m /. (m + n)))))))
  (h7 : (Even n) → (1 ∈ (lpMinimumPoints y)))
  : (Even n) → ((y (1 : ℝ)) = 0) := by
  sorry

theorem proof_gap_exercise_1417_4_5
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (x : ℝ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ m) * ((1 - x_1) ^ n))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((x_1 ^ (m - 1)) * ((1 - x_1) ^ (n - 1))) * (m - ((m + n) * x_1)))))))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x_1) = 0)) → (((x_1 = 0) ∨ (x_1 = 1)) ∨ (x_1 = (m /. (m + n)))))))
  (h7 : (Even n) → (1 ∈ (lpMinimumPoints y)))
  (h8 : (Even n) → ((y (1 : ℝ)) = 0))
  : (Odd n) → (1 ∉ (lpMaximumPoints y)) := by
  sorry

theorem proof_gap_exercise_1417_4_6
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (x : ℝ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ m) * ((1 - x_1) ^ n))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((x_1 ^ (m - 1)) * ((1 - x_1) ^ (n - 1))) * (m - ((m + n) * x_1)))))))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x_1) = 0)) → (((x_1 = 0) ∨ (x_1 = 1)) ∨ (x_1 = (m /. (m + n)))))))
  (h7 : (Even n) → (1 ∈ (lpMinimumPoints y)))
  (h8 : (Even n) → ((y (1 : ℝ)) = 0))
  (h9 : (Odd n) → (1 ∉ (lpMaximumPoints y)))
  : (Odd n) → (1 ∉ (lpMinimumPoints y)) := by
  sorry

theorem proof_gap_exercise_1417_4_7
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (x : ℝ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((x_1 ^ m) * ((1 - x_1) ^ n))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x_1) = (((x_1 ^ (m - 1)) * ((1 - x_1) ^ (n - 1))) * (m - ((m + n) * x_1)))))))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x_1) = 0)) → (((x_1 = 0) ∨ (x_1 = 1)) ∨ (x_1 = (m /. (m + n)))))))
  (h7 : (Even n) → (1 ∈ (lpMinimumPoints y)))
  (h8 : (Even n) → ((y (1 : ℝ)) = 0))
  (h9 : (Odd n) → (1 ∉ (lpMaximumPoints y)))
  (h10 : (Odd n) → (1 ∉ (lpMinimumPoints y)))
  : (((Even n) → ((1 ∈ (lpMinimumPoints y)) ∧ ((y (1 : ℝ)) = 0))) ∧ ((Odd n) → ((1 ∉ (lpMaximumPoints y)) ∧ (1 ∉ (lpMinimumPoints y))))) → (x = 1) := by
  sorry
