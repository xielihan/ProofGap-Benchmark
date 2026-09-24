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

-- exercise: exercise_1417_3

theorem proof_gap_exercise_1417_3_1
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x ^ m) * ((1 - x) ^ n))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((x ^ (m - 1)) * ((1 - x) ^ (n - 1))) * (m - ((m + n) * x)))))) := by
  sorry

theorem proof_gap_exercise_1417_3_2
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x ^ m) * ((1 - x) ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((x ^ (m - 1)) * ((1 - x) ^ (n - 1))) * (m - ((m + n) * x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x) = 0)) → (((x = 0) ∨ (x = 1)) ∨ (x = (m /. (m + n)))))) := by
  sorry

theorem proof_gap_exercise_1417_3_3
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x ^ m) * ((1 - x) ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((x ^ (m - 1)) * ((1 - x) ^ (n - 1))) * (m - ((m + n) * x)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x) = 0)) → (((x = 0) ∨ (x = 1)) ∨ (x = (m /. (m + n)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (m /. (m + n)))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1417_3_4
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x ^ m) * ((1 - x) ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((x ^ (m - 1)) * ((1 - x) ^ (n - 1))) * (m - ((m + n) * x)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x) = 0)) → (((x = 0) ∨ (x = 1)) ∨ (x = (m /. (m + n)))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (m /. (m + n)))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((m /. (m + n)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1417_3_5
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x ^ m) * ((1 - x) ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((x ^ (m - 1)) * ((1 - x) ^ (n - 1))) * (m - ((m + n) * x)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x) = 0)) → (((x = 0) ∨ (x = 1)) ∨ (x = (m /. (m + n)))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (m /. (m + n)))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((m /. (m + n)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  : (m /. (m + n)) ∈ (lpMaximumPoints y) := by
  sorry

theorem proof_gap_exercise_1417_3_6
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x ^ m) * ((1 - x) ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((x ^ (m - 1)) * ((1 - x) ^ (n - 1))) * (m - ((m + n) * x)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x) = 0)) → (((x = 0) ∨ (x = 1)) ∨ (x = (m /. (m + n)))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (m /. (m + n)))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((m /. (m + n)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h10 : (m /. (m + n)) ∈ (lpMaximumPoints y))
  : (y (m /. (m + n))) = (((m ^ m) * (n ^ n)) /. ((m + n) ^ (m + n))) := by
  sorry

theorem proof_gap_exercise_1417_3_7
  (y : (ℝ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h4 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((y x) = ((x ^ m) * ((1 - x) ^ n))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => y t) x) = (((x ^ (m - 1)) * ((1 - x) ^ (n - 1))) * (m - ((m + n) * x)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => y t) x) = 0)) → (((x = 0) ∨ (x = 1)) ∨ (x = (m /. (m + n)))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < (m /. (m + n)))) → ((iteratedDeriv 1 (fun t => y t) x) > 0))))
  (h9 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((m /. (m + n)) < x)) ∧ (x < 1)) → ((iteratedDeriv 1 (fun t => y t) x) < 0))))
  (h10 : (m /. (m + n)) ∈ (lpMaximumPoints y))
  (h11 : (y (m /. (m + n))) = (((m ^ m) * (n ^ n)) /. ((m + n) ^ (m + n))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = (m /. (m + n)))) → (x ∈ (lpMaximumPoints y)))) := by
  sorry
