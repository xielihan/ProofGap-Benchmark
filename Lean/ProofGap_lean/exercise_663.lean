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

-- exercise: exercise_663

theorem proof_gap_exercise_663_1
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h3 : x > 0)
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = (x_1 ^ (2 : ℕ))))))
  (h5 : 0 < v_uCE_uB5)
  (h6 : v_uCE_uB5 < 100)
  : (|(((y x) - 100))| < 1) → ((99 < (x ^ (2 : ℕ))) ∧ ((x ^ (2 : ℕ)) < 101)) := by
  sorry

theorem proof_gap_exercise_663_2
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h3 : x > 0)
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = (x_1 ^ (2 : ℕ))))))
  (h5 : 0 < v_uCE_uB5)
  (h6 : v_uCE_uB5 < 100)
  (h7 : (|(((y x) - 100))| < 1) → ((99 < (x ^ (2 : ℕ))) ∧ ((x ^ (2 : ℕ)) < 101)))
  : (|(((y x) - 100))| < 1) → (((Real.rpow (99 : ℝ) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (101 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_663_3
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h3 : x > 0)
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = (x_1 ^ (2 : ℕ))))))
  (h5 : 0 < v_uCE_uB5)
  (h6 : v_uCE_uB5 < 100)
  (h7 : (|(((y x) - 100))| < 1) → ((99 < (x ^ (2 : ℕ))) ∧ ((x ^ (2 : ℕ)) < 101)))
  (h8 : (|(((y x) - 100))| < 1) → (((Real.rpow (99 : ℝ) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (101 : ℝ) (((2 : ℝ))⁻¹)))))
  : (|(((y x) - 100))| < (((01 : ℝ) /. (10 : ℝ)))) → (((Real.rpow (100 - (((01 : ℝ) /. (10 : ℝ)))) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + (((01 : ℝ) /. (10 : ℝ)))) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_663_4
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h3 : x > 0)
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = (x_1 ^ (2 : ℕ))))))
  (h5 : 0 < v_uCE_uB5)
  (h6 : v_uCE_uB5 < 100)
  (h7 : (|(((y x) - 100))| < 1) → ((99 < (x ^ (2 : ℕ))) ∧ ((x ^ (2 : ℕ)) < 101)))
  (h8 : (|(((y x) - 100))| < 1) → (((Real.rpow (99 : ℝ) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (101 : ℝ) (((2 : ℝ))⁻¹)))))
  (h9 : (|(((y x) - 100))| < (((01 : ℝ) /. (10 : ℝ)))) → (((Real.rpow (100 - (((01 : ℝ) /. (10 : ℝ)))) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + (((01 : ℝ) /. (10 : ℝ)))) (((2 : ℝ))⁻¹)))))
  : (|(((y x) - 100))| < (((001 : ℝ) /. (100 : ℝ)))) → (((Real.rpow (100 - (((001 : ℝ) /. (100 : ℝ)))) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + (((001 : ℝ) /. (100 : ℝ)))) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_663_5
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h3 : x > 0)
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = (x_1 ^ (2 : ℕ))))))
  (h5 : 0 < v_uCE_uB5)
  (h6 : v_uCE_uB5 < 100)
  (h7 : (|(((y x) - 100))| < 1) → ((99 < (x ^ (2 : ℕ))) ∧ ((x ^ (2 : ℕ)) < 101)))
  (h8 : (|(((y x) - 100))| < 1) → (((Real.rpow (99 : ℝ) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (101 : ℝ) (((2 : ℝ))⁻¹)))))
  (h9 : (|(((y x) - 100))| < (((01 : ℝ) /. (10 : ℝ)))) → (((Real.rpow (100 - (((01 : ℝ) /. (10 : ℝ)))) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + (((01 : ℝ) /. (10 : ℝ)))) (((2 : ℝ))⁻¹)))))
  (h10 : (|(((y x) - 100))| < (((001 : ℝ) /. (100 : ℝ)))) → (((Real.rpow (100 - (((001 : ℝ) /. (100 : ℝ)))) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + (((001 : ℝ) /. (100 : ℝ)))) (((2 : ℝ))⁻¹)))))
  : (|(((y x) - 100))| < v_uCE_uB5) → (((Real.rpow (100 - v_uCE_uB5) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + v_uCE_uB5) (((2 : ℝ))⁻¹)))) := by
  sorry

theorem proof_gap_exercise_663_6
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (v_uCE_uB5 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB5 ∈ (Set.univ : Set ℝ))
  (h3 : x > 0)
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 > 0)) → ((y x_1) = (x_1 ^ (2 : ℕ))))))
  (h5 : 0 < v_uCE_uB5)
  (h6 : v_uCE_uB5 < 100)
  (h7 : (|(((y x) - 100))| < 1) → ((99 < (x ^ (2 : ℕ))) ∧ ((x ^ (2 : ℕ)) < 101)))
  (h8 : (|(((y x) - 100))| < 1) → (((Real.rpow (99 : ℝ) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (101 : ℝ) (((2 : ℝ))⁻¹)))))
  (h9 : (|(((y x) - 100))| < (((01 : ℝ) /. (10 : ℝ)))) → (((Real.rpow (100 - (((01 : ℝ) /. (10 : ℝ)))) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + (((01 : ℝ) /. (10 : ℝ)))) (((2 : ℝ))⁻¹)))))
  (h10 : (|(((y x) - 100))| < (((001 : ℝ) /. (100 : ℝ)))) → (((Real.rpow (100 - (((001 : ℝ) /. (100 : ℝ)))) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + (((001 : ℝ) /. (100 : ℝ)))) (((2 : ℝ))⁻¹)))))
  (h11 : (|(((y x) - 100))| < v_uCE_uB5) → (((Real.rpow (100 - v_uCE_uB5) (((2 : ℝ))⁻¹)) < x) ∧ (x < (Real.rpow (100 + v_uCE_uB5) (((2 : ℝ))⁻¹)))))
  : (((((((((((995 : ℝ) /. (100 : ℝ))) < x) ∧ (x < (((1005 : ℝ) /. (100 : ℝ))))) ∧ ((((9995 : ℝ) /. (1000 : ℝ))) < x)) ∧ (x < (((10005 : ℝ) /. (1000 : ℝ))))) ∧ ((((99995 : ℝ) /. (10000 : ℝ))) < x)) ∧ (x < (((100005 : ℝ) /. (10000 : ℝ))))) ∧ ((Real.rpow (100 - v_uCE_uB5) (((2 : ℝ))⁻¹)) < x)) ∧ (x < (Real.rpow (100 + v_uCE_uB5) (((2 : ℝ))⁻¹)))) ↔ ((((|(((y x) - 100))| < 1) ∧ (|(((y x) - 100))| < (((01 : ℝ) /. (10 : ℝ))))) ∧ (|(((y x) - 100))| < (((001 : ℝ) /. (100 : ℝ))))) ∧ (|(((y x) - 100))| < v_uCE_uB5)) := by
  sorry
