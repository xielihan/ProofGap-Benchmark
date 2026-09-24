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

-- exercise: exercise_2491

theorem proof_gap_exercise_2491_1
  (y_1 : (ℝ -> ℝ))
  (y_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (P_x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b ≥ a))
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → (P_x = (((2 * Real.pi) * (∫ x_1 in (-a)..a, (((b + (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (a /. (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))) + ((2 * Real.pi) * (∫ x_1 in (-a)..a, (((b - (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (a /. (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((y_1 x) = (b + (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_2491_2
  (y_1 : (ℝ -> ℝ))
  (y_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (P_x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b ≥ a))
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((y_1 x) = (b + (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → (P_x = (((2 * Real.pi) * (∫ x_1 in (-a)..a, (((b + (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (a /. (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))) + ((2 * Real.pi) * (∫ x_1 in (-a)..a, (((b - (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (a /. (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((y_2 x) = (b - (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_2491_3
  (y_1 : (ℝ -> ℝ))
  (y_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (P_x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b ≥ a))
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((y_1 x) = (b + (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((y_2 x) = (b - (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → (P_x = (((2 * Real.pi) * (∫ x_1 in (-a)..a, (((b + (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (a /. (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))) + ((2 * Real.pi) * (∫ x_1 in (-a)..a, (((b - (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (a /. (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))))))) := by
  sorry

theorem proof_gap_exercise_2491_4
  (y_1 : (ℝ -> ℝ))
  (y_2 : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (P_x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b ≥ a))
  (h3 : P_x ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((y_1 x) = (b + (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → ((y_2 x) = (b - (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))))))
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ ((-a) ≤ x)) ∧ (x ≤ a)) → (P_x = (((2 * Real.pi) * (∫ x_1 in (-a)..a, (((b + (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (a /. (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))) + ((2 * Real.pi) * (∫ x_1 in (-a)..a, (((b - (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (a /. (Real.rpow ((a ^ (2 : ℕ)) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) * (1 : ℝ)))))))))
  (h7 : (∫ x in (-a)..a, ((a /. (Real.rpow ((a ^ (2 : ℕ)) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = Real.pi)
  : P_x = (((4 * (Real.pi ^ (2 : ℕ))) * a) * b) := by
  sorry
