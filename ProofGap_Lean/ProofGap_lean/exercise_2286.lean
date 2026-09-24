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

-- exercise: exercise_2286

theorem proof_gap_exercise_2286_1
  (I : (ℕ -> ℝ))
  (m : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : m > (-(1 : ℝ)))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = (((((1 /. (m + 1)) * (Real.rpow (1 : ℝ) (m + 1))) * ((Real.log (1 : ℝ)) ^ n)) - (((1 /. (m + 1)) * (Real.rpow (0 : ℝ) (m + 1))) * ((Real.log (0 : ℝ)) ^ n))) - ((n /. (m + 1)) * (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ (n - 1))) * (1 : ℝ)))))))) := by
  sorry

theorem proof_gap_exercise_2286_2
  (I : (ℕ -> ℝ))
  (m : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : m > (-(1 : ℝ)))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = (((((1 /. (m + 1)) * (Real.rpow (1 : ℝ) (m + 1))) * ((Real.log (1 : ℝ)) ^ n)) - (((1 /. (m + 1)) * (Real.rpow (0 : ℝ) (m + 1))) * ((Real.log (0 : ℝ)) ^ n))) - ((n /. (m + 1)) * (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ (n - 1))) * (1 : ℝ)))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((-(n /. (m + 1))) * (I (n - 1)))))) := by
  sorry

theorem proof_gap_exercise_2286_3
  (I : (ℕ -> ℝ))
  (m : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : m > (-(1 : ℝ)))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = (((((1 /. (m + 1)) * (Real.rpow (1 : ℝ) (m + 1))) * ((Real.log (1 : ℝ)) ^ n)) - (((1 /. (m + 1)) * (Real.rpow (0 : ℝ) (m + 1))) * ((Real.log (0 : ℝ)) ^ n))) - ((n /. (m + 1)) * (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ (n - 1))) * (1 : ℝ)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((-(n /. (m + 1))) * (I (n - 1)))))))
  : (I (0 : ℕ)) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2286_4
  (I : (ℕ -> ℝ))
  (m : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : m > (-(1 : ℝ)))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = (((((1 /. (m + 1)) * (Real.rpow (1 : ℝ) (m + 1))) * ((Real.log (1 : ℝ)) ^ n)) - (((1 /. (m + 1)) * (Real.rpow (0 : ℝ) (m + 1))) * ((Real.log (0 : ℝ)) ^ n))) - ((n /. (m + 1)) * (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ (n - 1))) * (1 : ℝ)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((-(n /. (m + 1))) * (I (n - 1)))))))
  (h6 : (I (0 : ℕ)) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))) = (1 /. (m + 1)) := by
  sorry

theorem proof_gap_exercise_2286_5
  (I : (ℕ -> ℝ))
  (m : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : m > (-(1 : ℝ)))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = (((((1 /. (m + 1)) * (Real.rpow (1 : ℝ) (m + 1))) * ((Real.log (1 : ℝ)) ^ n)) - (((1 /. (m + 1)) * (Real.rpow (0 : ℝ) (m + 1))) * ((Real.log (0 : ℝ)) ^ n))) - ((n /. (m + 1)) * (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ (n - 1))) * (1 : ℝ)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((-(n /. (m + 1))) * (I (n - 1)))))))
  (h6 : (I (0 : ℕ)) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))) = (1 /. (m + 1)))
  : (I (0 : ℕ)) = (1 /. (m + 1)) := by
  sorry

theorem proof_gap_exercise_2286_6
  (I : (ℕ -> ℝ))
  (m : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : m > (-(1 : ℝ)))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = (((((1 /. (m + 1)) * (Real.rpow (1 : ℝ) (m + 1))) * ((Real.log (1 : ℝ)) ^ n)) - (((1 /. (m + 1)) * (Real.rpow (0 : ℝ) (m + 1))) * ((Real.log (0 : ℝ)) ^ n))) - ((n /. (m + 1)) * (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ (n - 1))) * (1 : ℝ)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((-(n /. (m + 1))) * (I (n - 1)))))))
  (h6 : (I (0 : ℕ)) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))) = (1 /. (m + 1)))
  (h8 : (I (0 : ℕ)) = (1 /. (m + 1)))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((∏ k ∈ Finset.Icc (1 : ℕ) n, (-(k /. (m + 1)))) * (I (0 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_2286_7
  (I : (ℕ -> ℝ))
  (m : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : m > (-(1 : ℝ)))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = (((((1 /. (m + 1)) * (Real.rpow (1 : ℝ) (m + 1))) * ((Real.log (1 : ℝ)) ^ n)) - (((1 /. (m + 1)) * (Real.rpow (0 : ℝ) (m + 1))) * ((Real.log (0 : ℝ)) ^ n))) - ((n /. (m + 1)) * (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ (n - 1))) * (1 : ℝ)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((-(n /. (m + 1))) * (I (n - 1)))))))
  (h6 : (I (0 : ℕ)) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))) = (1 /. (m + 1)))
  (h8 : (I (0 : ℕ)) = (1 /. (m + 1)))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((∏ k ∈ Finset.Icc (1 : ℕ) n, (-(k /. (m + 1)))) * (I (0 : ℕ)))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((m + 1) ^ (n + 1))))))) := by
  sorry

theorem proof_gap_exercise_2286_8
  (I : (ℕ -> ℝ))
  (m : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : m > (-(1 : ℝ)))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = (((((1 /. (m + 1)) * (Real.rpow (1 : ℝ) (m + 1))) * ((Real.log (1 : ℝ)) ^ n)) - (((1 /. (m + 1)) * (Real.rpow (0 : ℝ) (m + 1))) * ((Real.log (0 : ℝ)) ^ n))) - ((n /. (m + 1)) * (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ (n - 1))) * (1 : ℝ)))))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((-(n /. (m + 1))) * (I (n - 1)))))))
  (h6 : (I (0 : ℕ)) = (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow x m) * (1 : ℝ))) = (1 /. (m + 1)))
  (h8 : (I (0 : ℕ)) = (1 /. (m + 1)))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((I n) = ((∏ k ∈ Finset.Icc (1 : ℕ) n, (-(k /. (m + 1)))) * (I (0 : ℕ)))))))
  (h10 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((m + 1) ^ (n + 1))))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (((-(1 : ℤ)) ^ n) * ((n)! /. ((m + 1) ^ (n + 1))))))) → (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((I n) = (∫ x in (0 : ℝ)..(1 : ℝ), (((Real.rpow x m) * ((Real.log x) ^ n)) * (1 : ℝ)))))) := by
  sorry
