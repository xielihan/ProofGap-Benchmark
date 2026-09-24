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

-- exercise: exercise_2299

theorem proof_gap_exercise_2299_1
  (B : (ℕ × ℕ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : (forall (m_1 : ℕ) (n_1 : ℕ), (((((m_1 ∈ (Set.univ : Set ℕ)) ∧ (m_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (n_1 ∈ (Set.univ : Set ℕ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((B (m_1, n_1)) = (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (m_1 - 1)) * ((1 - x) ^ (n_1 - 1))) * (1 : ℝ)))))))
  : (n ≥ 2) → ((B (m, n)) = (((((1 /. m) * ((1 : ℕ) ^ m)) * ((1 - 1) ^ (n - 1))) - (((1 /. m) * ((0 : ℕ) ^ m)) * ((1 - 0) ^ (n - 1)))) + (((n - 1) /. m) * (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ m) * ((1 - x) ^ (n - 2))) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2299_2
  (B : (ℕ × ℕ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : (forall (m_1 : ℕ) (n_1 : ℕ), (((((m_1 ∈ (Set.univ : Set ℕ)) ∧ (m_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (n_1 ∈ (Set.univ : Set ℕ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((B (m_1, n_1)) = (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (m_1 - 1)) * ((1 - x) ^ (n_1 - 1))) * (1 : ℝ)))))))
  (h4 : (n ≥ 2) → ((B (m, n)) = (((((1 /. m) * ((1 : ℕ) ^ m)) * ((1 - 1) ^ (n - 1))) - (((1 /. m) * ((0 : ℕ) ^ m)) * ((1 - 0) ^ (n - 1)))) + (((n - 1) /. m) * (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ m) * ((1 - x) ^ (n - 2))) * (1 : ℝ)))))))
  : (n ≥ 2) → ((B (m, n)) = (((n - 1) /. m) * (B ((m + 1), (n - 1))))) := by
  sorry

theorem proof_gap_exercise_2299_3
  (B : (ℕ × ℕ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : (forall (m_1 : ℕ) (n_1 : ℕ), (((((m_1 ∈ (Set.univ : Set ℕ)) ∧ (m_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (n_1 ∈ (Set.univ : Set ℕ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((B (m_1, n_1)) = (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (m_1 - 1)) * ((1 - x) ^ (n_1 - 1))) * (1 : ℝ)))))))
  (h4 : (n ≥ 2) → ((B (m, n)) = (((((1 /. m) * ((1 : ℕ) ^ m)) * ((1 - 1) ^ (n - 1))) - (((1 /. m) * ((0 : ℕ) ^ m)) * ((1 - 0) ^ (n - 1)))) + (((n - 1) /. m) * (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ m) * ((1 - x) ^ (n - 2))) * (1 : ℝ)))))))
  (h5 : (n ≥ 2) → ((B (m, n)) = (((n - 1) /. m) * (B ((m + 1), (n - 1))))))
  : (B (m, n)) = ((((n - 1))! /. (((m * (m + 1)) * (m + 2)) * ((m + n) - 2))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ ((m + n) - 2)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2299_4
  (B : (ℕ × ℕ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : m ∈ ({n_1 : ℕ | 0 < n_1}))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (m_1 : ℕ) (n_1 : ℕ), (((m_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((B (m_1, n_1)) = (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (m_1 - 1)) * ((1 - x) ^ (n_1 - 1))) * (1 : ℝ)))))))
  (h4 : (n ≥ 2) → ((B (m, n)) = (((((1 /. m) * ((1 : ℕ) ^ m)) * ((1 - 1) ^ (n - 1))) - (((1 /. m) * ((0 : ℕ) ^ m)) * ((1 - 0) ^ (n - 1)))) + (((n - 1) /. m) * (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ m) * ((1 - x) ^ (n - 2))) * (1 : ℝ)))))))
  (h5 : (n ≥ 2) → ((B (m, n)) = (((n - 1) /. m) * (B ((m + 1), (n - 1))))))
  (h6 : (B (m, n)) = ((((n - 1))! /. (((m * (m + 1)) * (m + 2)) * ((m + n) - 2))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ ((m + n) - 2)) * (1 : ℝ)))))
  (h7 : (m ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ ((m + n) - 2)) * (1 : ℝ))) = (((1 /. ((m + n) - 1)) * ((1 : ℕ) ^ ((m + n) - 1))) - ((1 /. ((m + n) - 1)) * ((0 : ℕ) ^ ((m + n) - 1)))) := by
  sorry

theorem proof_gap_exercise_2299_5
  (B : (ℕ × ℕ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : (forall (m_1 : ℕ) (n_1 : ℕ), (((((m_1 ∈ (Set.univ : Set ℕ)) ∧ (m_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (n_1 ∈ (Set.univ : Set ℕ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((B (m_1, n_1)) = (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (m_1 - 1)) * ((1 - x) ^ (n_1 - 1))) * (1 : ℝ)))))))
  (h4 : (n ≥ 2) → ((B (m, n)) = (((((1 /. m) * ((1 : ℕ) ^ m)) * ((1 - 1) ^ (n - 1))) - (((1 /. m) * ((0 : ℕ) ^ m)) * ((1 - 0) ^ (n - 1)))) + (((n - 1) /. m) * (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ m) * ((1 - x) ^ (n - 2))) * (1 : ℝ)))))))
  (h5 : (n ≥ 2) → ((B (m, n)) = (((n - 1) /. m) * (B ((m + 1), (n - 1))))))
  (h6 : (B (m, n)) = ((((n - 1))! /. (((m * (m + 1)) * (m + 2)) * ((m + n) - 2))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ ((m + n) - 2)) * (1 : ℝ)))))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ ((m + n) - 2)) * (1 : ℝ))) = (((1 /. ((m + n) - 1)) * ((1 : ℕ) ^ ((m + n) - 1))) - ((1 /. ((m + n) - 1)) * ((0 : ℕ) ^ ((m + n) - 1)))))
  : (B (m, n)) = (((((((n - 1))! * ((m - 1))!) /. (((m + n) - 2))!) * (1 /. ((m + n) - 1))) * ((1 : ℕ) ^ ((m + n) - 1))) - ((((((n - 1))! * ((m - 1))!) /. (((m + n) - 2))!) * (1 /. ((m + n) - 1))) * ((0 : ℕ) ^ ((m + n) - 1)))) := by
  sorry

theorem proof_gap_exercise_2299_6
  (B : (ℕ × ℕ -> ℝ))
  (m : ℕ)
  (n : ℕ)
  (h1 : (m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1})))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1})))
  (h3 : (forall (m_1 : ℕ) (n_1 : ℕ), (((((m_1 ∈ (Set.univ : Set ℕ)) ∧ (m_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (n_1 ∈ (Set.univ : Set ℕ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((B (m_1, n_1)) = (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (m_1 - 1)) * ((1 - x) ^ (n_1 - 1))) * (1 : ℝ)))))))
  (h4 : (n ≥ 2) → ((B (m, n)) = (((((1 /. m) * ((1 : ℕ) ^ m)) * ((1 - 1) ^ (n - 1))) - (((1 /. m) * ((0 : ℕ) ^ m)) * ((1 - 0) ^ (n - 1)))) + (((n - 1) /. m) * (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ m) * ((1 - x) ^ (n - 2))) * (1 : ℝ)))))))
  (h5 : (n ≥ 2) → ((B (m, n)) = (((n - 1) /. m) * (B ((m + 1), (n - 1))))))
  (h6 : (B (m, n)) = ((((n - 1))! /. (((m * (m + 1)) * (m + 2)) * ((m + n) - 2))) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ ((m + n) - 2)) * (1 : ℝ)))))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), ((x ^ ((m + n) - 2)) * (1 : ℝ))) = (((1 /. ((m + n) - 1)) * ((1 : ℕ) ^ ((m + n) - 1))) - ((1 /. ((m + n) - 1)) * ((0 : ℕ) ^ ((m + n) - 1)))))
  (h8 : (B (m, n)) = (((((((n - 1))! * ((m - 1))!) /. (((m + n) - 2))!) * (1 /. ((m + n) - 1))) * ((1 : ℕ) ^ ((m + n) - 1))) - ((((((n - 1))! * ((m - 1))!) /. (((m + n) - 2))!) * (1 /. ((m + n) - 1))) * ((0 : ℕ) ^ ((m + n) - 1)))))
  : (B (m, n)) = ((((n - 1))! * ((m - 1))!) /. (((m + n) - 1))!) := by
  sorry
