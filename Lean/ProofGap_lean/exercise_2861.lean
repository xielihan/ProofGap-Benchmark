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

-- exercise: exercise_2861

theorem proof_gap_exercise_2861_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((1 - x) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = (1 /. ((1 - x) - (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = (1 /. ((5 /. 4) - ((x + (1 /. 2)) ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_2861_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((1 - x) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = (1 /. ((1 - x) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = (1 /. ((5 /. 4) - ((x + (1 /. 2)) ^ (2 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * ((1 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - (x + (1 /. 2)))) + (1 /. ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) /. 2) + x) + (1 /. 2)))))))) := by
  sorry

theorem proof_gap_exercise_2861_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((1 - x) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = (1 /. ((1 - x) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = (1 /. ((5 /. 4) - ((x + (1 /. 2)) ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * ((1 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - (x + (1 /. 2)))) + (1 /. ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) /. 2) + x) + (1 /. 2)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) * ((1 - ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) * x)) ^ (-(1 : ℤ)))) + ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) * ((1 + ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) * x)) ^ (-(1 : ℤ))))))))) := by
  sorry

theorem proof_gap_exercise_2861_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((1 - x) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = (1 /. ((1 - x) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = (1 /. ((5 /. 4) - ((x + (1 /. 2)) ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * ((1 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - (x + (1 /. 2)))) + (1 /. ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) /. 2) + x) + (1 /. 2)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) * ((1 - ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) * x)) ^ (-(1 : ℤ)))) + ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) * ((1 + ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) * x)) ^ (-(1 : ℤ))))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (∑' n, if (0 : ℕ) ≤ n then ((((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) ^ (n + 1)) + (((-(1 : ℤ)) ^ n) * ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) ^ (n + 1)))) * (x ^ n)) else 0))))) := by
  sorry

theorem proof_gap_exercise_2861_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((1 - x) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = (1 /. ((1 - x) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = (1 /. ((5 /. 4) - ((x + (1 /. 2)) ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * ((1 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - (x + (1 /. 2)))) + (1 /. ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) /. 2) + x) + (1 /. 2)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) * ((1 - ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) * x)) ^ (-(1 : ℤ)))) + ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) * ((1 + ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) * x)) ^ (-(1 : ℤ))))))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (∑' n, if (0 : ℕ) ≤ n then ((((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) ^ (n + 1)) + (((-(1 : ℤ)) ^ n) * ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) ^ (n + 1)))) * (x ^ n)) else 0))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (∑' n, if (0 : ℕ) ≤ n then ((((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1) /. 2) ^ (n + 1)) + (((-(1 : ℤ)) ^ n) * ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2) ^ (n + 1)))) * (x ^ n)) else 0))))) := by
  sorry

theorem proof_gap_exercise_2861_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((1 - x) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = (1 /. ((1 - x) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = (1 /. ((5 /. 4) - ((x + (1 /. 2)) ^ (2 : ℕ))))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * ((1 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - (x + (1 /. 2)))) + (1 /. ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) /. 2) + x) + (1 /. 2)))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) * ((1 - ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) * x)) ^ (-(1 : ℤ)))) + ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) * ((1 + ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) * x)) ^ (-(1 : ℤ))))))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (∑' n, if (0 : ℕ) ≤ n then ((((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1)) ^ (n + 1)) + (((-(1 : ℤ)) ^ n) * ((2 /. ((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1)) ^ (n + 1)))) * (x ^ n)) else 0))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (∑' n, if (0 : ℕ) ≤ n then ((((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1) /. 2) ^ (n + 1)) + (((-(1 : ℤ)) ^ n) * ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2) ^ (n + 1)))) * (x ^ n)) else 0))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (∑' n, if (0 : ℕ) ≤ n then ((((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1) /. 2) ^ (n + 1)) + (((-(1 : ℤ)) ^ n) * ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2) ^ (n + 1)))) * (x ^ n)) else 0))))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < (((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2))) → ((f x) = ((1 /. (Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹))) * (∑' n, if (0 : ℕ) ≤ n then ((((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) + 1) /. 2) ^ (n + 1)) + (((-(1 : ℤ)) ^ n) * ((((Real.rpow (5 : ℝ) (((2 : ℝ))⁻¹)) - 1) /. 2) ^ (n + 1)))) * (x ^ n)) else 0))))) := by
  sorry
