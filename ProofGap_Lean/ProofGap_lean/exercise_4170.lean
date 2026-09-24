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

-- exercise: exercise_4170

theorem proof_gap_exercise_4170_1
  (p : ℝ)
  (I : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : I ∈ (Set.univ : Set ℝ))
  (h3 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4170_2
  (p : ℝ)
  (I : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : I ∈ (Set.univ : Set ℝ))
  (h3 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h4 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  : (p > 1) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) = (1 /. (p - 1))))) := by
  sorry

theorem proof_gap_exercise_4170_3
  (p : ℝ)
  (I : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : I ∈ (Set.univ : Set ℝ))
  (h3 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h4 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h5 : (p > 1) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) = (1 /. (p - 1))))))
  : (p > 1) → (I = (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (p - (1 : ℝ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4170_4
  (p : ℝ)
  (I : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : I ∈ (Set.univ : Set ℝ))
  (h3 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h4 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h5 : (p > 1) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) = (1 /. (p - 1))))))
  (h6 : (p > 1) → (I = (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (p - (1 : ℝ))) * (1 : ℝ)))))
  : (p > 1) → (I = (1 /. (p - 1))) := by
  sorry

theorem proof_gap_exercise_4170_5
  (p : ℝ)
  (I : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : I ∈ (Set.univ : Set ℝ))
  (h3 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h4 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h5 : (p > 1) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) = (1 /. (p - 1))))))
  (h6 : (p > 1) → (I = (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (p - (1 : ℝ))) * (1 : ℝ)))))
  (h7 : (p > 1) → (I = (1 /. (p - 1))))
  : (p ≤ 1) → ((I : EReal) = ⊤) := by
  sorry

theorem proof_gap_exercise_4170_6
  (p : ℝ)
  (I : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : I ∈ (Set.univ : Set ℝ))
  (h3 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h4 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h5 : (p > 1) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) = (1 /. (p - 1))))))
  (h6 : (p > 1) → (I = (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (p - (1 : ℝ))) * (1 : ℝ)))))
  (h7 : (p > 1) → (I = (1 /. (p - 1))))
  (h8 : (p ≤ 1) → ((I : EReal) = ⊤))
  : (p > 1) → (I = (1 /. (p - 1))) := by
  sorry

theorem proof_gap_exercise_4170_7
  (p : ℝ)
  (I : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : I ∈ (Set.univ : Set ℝ))
  (h3 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h4 : I = (∫ x in (0 : ℝ)..(1 : ℝ), ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) * (1 : ℝ))))
  (h5 : (p > 1) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 1)) → ((∫ y in Set.Ioi (1 - x), (((1 : ℝ) /. (Real.rpow (x + y) p)) * (1 : ℝ))) = (1 /. (p - 1))))))
  (h6 : (p > 1) → (I = (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (p - (1 : ℝ))) * (1 : ℝ)))))
  (h7 : (p > 1) → (I = (1 /. (p - 1))))
  (h8 : (p ≤ 1) → ((I : EReal) = ⊤))
  (h9 : (p > 1) → (I = (1 /. (p - 1))))
  : (p ≤ 1) → ((I : EReal) = ⊤) := by
  sorry
