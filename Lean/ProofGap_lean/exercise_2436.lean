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

-- exercise: exercise_2436

theorem proof_gap_exercise_2436_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (s : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : s ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ b)
  (h5 : b < a)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((y x) = (a * (Real.log ((a ^ (2 : ℕ)) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((Real.rpow (1 + ((iteratedDeriv 1 (fun t => y t) x) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) = (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * a) * x) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_2436_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (s : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : s ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ b)
  (h5 : b < a)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((y x) = (a * (Real.log ((a ^ (2 : ℕ)) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * a) * x) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((Real.rpow (1 + ((iteratedDeriv 1 (fun t => y t) x) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) = (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_2436_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (s : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : s ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ b)
  (h5 : b < a)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((y x) = (a * (Real.log ((a ^ (2 : ℕ)) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * a) * x) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((Real.rpow (1 + ((iteratedDeriv 1 (fun t => y t) x) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) = (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))
  (h9 : s = ((a * (Real.log ((a + b) /. (a - b)))) - b))
  : s = (∫ x in (0 : ℝ)..b, ((((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ)))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2436_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (s : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : s ∈ (Set.univ : Set ℝ))
  (h4 : 0 ≤ b)
  (h5 : b < a)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((y x) = (a * (Real.log ((a ^ (2 : ℕ)) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((iteratedDeriv 1 (fun t => y t) x) = (((2 * a) * x) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ b)) → ((Real.rpow (1 + ((iteratedDeriv 1 (fun t => y t) x) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) = (((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))))))))
  (h9 : s = (∫ x in (0 : ℝ)..b, ((((a ^ (2 : ℕ)) + (x ^ (2 : ℕ))) /. ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ)))) * (1 : ℝ))))
  : s = ((a * (Real.log ((a + b) /. (a - b)))) - b) := by
  sorry
