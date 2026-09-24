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

-- exercise: exercise_3860

theorem proof_gap_exercise_3860_1
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_3860_2
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h4 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  : (n > 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma ((m + 1) /. n))))) := by
  sorry

theorem proof_gap_exercise_3860_3
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h4 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h5 : (n > 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (Gamma ((m + 1) /. n))))) := by
  sorry

theorem proof_gap_exercise_3860_4
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h4 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h5 : (n > 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h6 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h7 : (n < 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_3860_5
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h4 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h5 : (n > 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h6 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h7 : (n < 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h8 : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  : (n < 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_3860_6
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h4 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h5 : (n > 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h6 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h7 : (n < 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h8 : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h9 : (n < 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  : (n < 0) → ((((m + 1) /. n) > 0) → (((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (Gamma ((m + 1) /. n))))) := by
  sorry

theorem proof_gap_exercise_3860_7
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h4 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h5 : (n > 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h6 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h7 : (n < 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h8 : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h9 : (n < 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h10 : (n < 0) → ((((m + 1) /. n) > 0) → (((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (Gamma ((m + 1) /. n))))))
  : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((-(1 /. n)) * (Gamma ((m + 1) /. n))))) := by
  sorry

theorem proof_gap_exercise_3860_8
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h4 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h5 : (n > 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h6 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h7 : (n < 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h8 : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h9 : (n < 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h10 : (n < 0) → ((((m + 1) /. n) > 0) → (((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (Gamma ((m + 1) /. n))))))
  (h11 : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((-(1 /. n)) * (Gamma ((m + 1) /. n))))))
  : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. |(n)|) * (Gamma ((m + 1) /. n))) := by
  sorry

theorem proof_gap_exercise_3860_9
  (Gamma : (ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : ((n ∈ (Set.univ : Set ℝ)) ∧ (n ≠ 0)) ∧ (((m + 1) /. n) > 0))
  (h3 : (n > 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h4 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h5 : (n > 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h6 : (n > 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (Gamma ((m + 1) /. n))))))
  (h7 : (n < 0) → ((((m + 1) /. n) > 0) → (t = (Real.rpow x n))))
  (h8 : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h9 : (n < 0) → ((((m + 1) /. n) > 0) → (((1 /. n) * (-∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))))))
  (h10 : (n < 0) → ((((m + 1) /. n) > 0) → (((-(1 /. n)) * (∫ t in Set.Ioi (0 : ℝ), (((Real.rpow t (((m + 1) /. n) - 1)) * (Real.exp (-t))) * (1 : ℝ)))) = ((-(1 /. n)) * (Gamma ((m + 1) /. n))))))
  (h11 : (n < 0) → ((((m + 1) /. n) > 0) → ((∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((-(1 /. n)) * (Gamma ((m + 1) /. n))))))
  (h12 : (∫ x in Set.Ioi (0 : ℝ), (((Real.rpow x m) * (Real.exp (-(Real.rpow x n)))) * (1 : ℝ))) = ((1 /. |(n)|) * (Gamma ((m + 1) /. n))))
  : (m, n) ∈ ({p : ℝ × ℝ | ((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 ≠ 0)) ∧ (((p.1 + 1) /. p.2) > 0))}) := by
  sorry
