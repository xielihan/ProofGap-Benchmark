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

-- exercise: exercise_192

theorem proof_gap_exercise_192_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  : (f (-(2 : ℝ))) = (1 - 2) := by
  sorry

theorem proof_gap_exercise_192_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  : (1 - 2) = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_192_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  : (f (-(2 : ℝ))) = (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_192_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  : (f (-(1 : ℝ))) = (1 - 1) := by
  sorry

theorem proof_gap_exercise_192_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  : (1 - 1) = 0 := by
  sorry

theorem proof_gap_exercise_192_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  : (f (-(1 : ℝ))) = 0 := by
  sorry

theorem proof_gap_exercise_192_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  : (f (0 : ℝ)) = (1 + 0) := by
  sorry

theorem proof_gap_exercise_192_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  (h8 : (f (0 : ℝ)) = (1 + 0))
  : (1 + 0) = 1 := by
  sorry

theorem proof_gap_exercise_192_9
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  (h8 : (f (0 : ℝ)) = (1 + 0))
  (h9 : (1 + 0) = 1)
  : (f (0 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_192_10
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  (h8 : (f (0 : ℝ)) = (1 + 0))
  (h9 : (1 + 0) = 1)
  (h10 : (f (0 : ℝ)) = 1)
  : (f (1 : ℝ)) = ((2 : ℕ) ^ (1 : ℕ)) := by
  sorry

theorem proof_gap_exercise_192_11
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  (h8 : (f (0 : ℝ)) = (1 + 0))
  (h9 : (1 + 0) = 1)
  (h10 : (f (0 : ℝ)) = 1)
  (h11 : (f (1 : ℝ)) = ((2 : ℕ) ^ (1 : ℕ)))
  : ((2 : ℕ) ^ (1 : ℕ)) = 2 := by
  sorry

theorem proof_gap_exercise_192_12
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  (h8 : (f (0 : ℝ)) = (1 + 0))
  (h9 : (1 + 0) = 1)
  (h10 : (f (0 : ℝ)) = 1)
  (h11 : (f (1 : ℝ)) = ((2 : ℕ) ^ (1 : ℕ)))
  (h12 : ((2 : ℕ) ^ (1 : ℕ)) = 2)
  : (f (1 : ℝ)) = 2 := by
  sorry

theorem proof_gap_exercise_192_13
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  (h8 : (f (0 : ℝ)) = (1 + 0))
  (h9 : (1 + 0) = 1)
  (h10 : (f (0 : ℝ)) = 1)
  (h11 : (f (1 : ℝ)) = ((2 : ℕ) ^ (1 : ℕ)))
  (h12 : ((2 : ℕ) ^ (1 : ℕ)) = 2)
  (h13 : (f (1 : ℝ)) = 2)
  : (f (2 : ℝ)) = ((2 : ℕ) ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_192_14
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  (h8 : (f (0 : ℝ)) = (1 + 0))
  (h9 : (1 + 0) = 1)
  (h10 : (f (0 : ℝ)) = 1)
  (h11 : (f (1 : ℝ)) = ((2 : ℕ) ^ (1 : ℕ)))
  (h12 : ((2 : ℕ) ^ (1 : ℕ)) = 2)
  (h13 : (f (1 : ℝ)) = 2)
  (h14 : (f (2 : ℝ)) = ((2 : ℕ) ^ (2 : ℕ)))
  : ((2 : ℕ) ^ (2 : ℕ)) = 4 := by
  sorry

theorem proof_gap_exercise_192_15
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if ((⊥ < (x : EReal)) ∧ (x ≤ 0)) then (1 + x) else (if ((0 < x) ∧ ((x : EReal) < ⊤)) then (Real.rpow (2 : ℝ) x) else (Real.rpow (2 : ℝ) x)))))))
  (h2 : (f (-(2 : ℝ))) = (1 - 2))
  (h3 : (1 - 2) = (-(1 : ℝ)))
  (h4 : (f (-(2 : ℝ))) = (-(1 : ℝ)))
  (h5 : (f (-(1 : ℝ))) = (1 - 1))
  (h6 : (1 - 1) = 0)
  (h7 : (f (-(1 : ℝ))) = 0)
  (h8 : (f (0 : ℝ)) = (1 + 0))
  (h9 : (1 + 0) = 1)
  (h10 : (f (0 : ℝ)) = 1)
  (h11 : (f (1 : ℝ)) = ((2 : ℕ) ^ (1 : ℕ)))
  (h12 : ((2 : ℕ) ^ (1 : ℕ)) = 2)
  (h13 : (f (1 : ℝ)) = 2)
  (h14 : (f (2 : ℝ)) = ((2 : ℕ) ^ (2 : ℕ)))
  (h15 : ((2 : ℕ) ^ (2 : ℕ)) = 4)
  : (f (2 : ℝ)) = 4 := by
  sorry
