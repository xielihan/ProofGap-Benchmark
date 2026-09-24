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

-- exercise: exercise_3859

theorem proof_gap_exercise_3859_1
  (Gamma : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h2 : t = (Real.rpow x n))
  : ((0 ≤ x) ∧ ((x : EReal) < ⊤)) → ((0 ≤ t) ∧ ((t : EReal) < ⊤)) := by
  sorry

theorem proof_gap_exercise_3859_2
  (Gamma : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h2 : t = (Real.rpow x n))
  (h3 : ((0 ≤ x) ∧ ((x : EReal) < ⊤)) → ((0 ≤ t) ∧ ((t : EReal) < ⊤)))
  : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3859_3
  (Gamma : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h2 : t = (Real.rpow x n))
  (h3 : ((0 ≤ x) ∧ ((x : EReal) < ⊤)) → ((0 ≤ t) ∧ ((t : EReal) < ⊤)))
  (h4 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))
  : ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma (1 /. n))) := by
  sorry

theorem proof_gap_exercise_3859_4
  (Gamma : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h2 : t = (Real.rpow x n))
  (h3 : ((0 ≤ x) ∧ ((x : EReal) < ⊤)) → ((0 ≤ t) ∧ ((t : EReal) < ⊤)))
  (h4 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))
  (h5 : ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma (1 /. n))))
  : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (Gamma (1 /. n))) := by
  sorry

theorem proof_gap_exercise_3859_5
  (Gamma : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h2 : t = (Real.rpow x n))
  (h3 : ((0 ≤ x) ∧ ((x : EReal) < ⊤)) → ((0 ≤ t) ∧ ((t : EReal) < ⊤)))
  (h4 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))
  (h5 : ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma (1 /. n))))
  (h6 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (Gamma (1 /. n))))
  : ((1 /. n) > 0) ↔ (n > 0) := by
  sorry

theorem proof_gap_exercise_3859_6
  (Gamma : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h2 : t = (Real.rpow x n))
  (h3 : ((0 ≤ x) ∧ ((x : EReal) < ⊤)) → ((0 ≤ t) ∧ ((t : EReal) < ⊤)))
  (h4 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))
  (h5 : ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma (1 /. n))))
  (h6 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (Gamma (1 /. n))))
  (h7 : ((1 /. n) > 0) ↔ (n > 0))
  : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (Gamma (1 /. n))) := by
  sorry

theorem proof_gap_exercise_3859_7
  (Gamma : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h2 : t = (Real.rpow x n))
  (h3 : ((0 ≤ x) ∧ ((x : EReal) < ⊤)) → ((0 ≤ t) ∧ ((t : EReal) < ⊤)))
  (h4 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))
  (h5 : ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t ((1 /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma (1 /. n))))
  (h6 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (Gamma (1 /. n))))
  (h7 : ((1 /. n) > 0) ↔ (n > 0))
  (h8 : (∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.rpow x n))) * (1 : ℝ))) = ((1 /. n) * (Gamma (1 /. n))))
  : n > 0 := by
  sorry
