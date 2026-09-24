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

-- exercise: exercise_2467

theorem proof_gap_exercise_2467_1
  (S : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V ∈ (Set.univ : Set ℝ))
  (h4 : a > 0)
  (h5 : b > 0)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = ((Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = (∫ y in (0 : ℝ)..(Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2467_2
  (S : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V ∈ (Set.univ : Set ℝ))
  (h4 : a > 0)
  (h5 : b > 0)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = (∫ y in (0 : ℝ)..(Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = ((Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_2467_3
  (S : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V ∈ (Set.univ : Set ℝ))
  (h4 : a > 0)
  (h5 : b > 0)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = (∫ y in (0 : ℝ)..(Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = ((Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, (((Real.rpow ((a * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x_1)) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, ((S x_1) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2467_4
  (S : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V ∈ (Set.univ : Set ℝ))
  (h4 : a > 0)
  (h5 : b > 0)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = (∫ y in (0 : ℝ)..(Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = ((Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, ((S x_1) * (1 : ℝ)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = ((Real.rpow b (((2 : ℝ))⁻¹)) * (∫ x_1 in (0 : ℝ)..a, (((Real.rpow x_1 (((2 : ℝ))⁻¹)) * (a - x_1)) * (1 : ℝ))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, (((Real.rpow ((a * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x_1)) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2467_5
  (S : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V ∈ (Set.univ : Set ℝ))
  (h4 : a > 0)
  (h5 : b > 0)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = (∫ y in (0 : ℝ)..(Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = ((Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, ((S x_1) * (1 : ℝ)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, (((Real.rpow ((a * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x_1)) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = ((Real.rpow b (((2 : ℝ))⁻¹)) * (∫ x_1 in (0 : ℝ)..a, (((Real.rpow x_1 (((2 : ℝ))⁻¹)) * (a - x_1)) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2467_6
  (S : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V ∈ (Set.univ : Set ℝ))
  (h4 : a > 0)
  (h5 : b > 0)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = (∫ y in (0 : ℝ)..(Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = ((Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, ((S x_1) * (1 : ℝ)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, (((Real.rpow ((a * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x_1)) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = ((Real.rpow b (((2 : ℝ))⁻¹)) * (∫ x_1 in (0 : ℝ)..a, (((Real.rpow x_1 (((2 : ℝ))⁻¹)) * (a - x_1)) * (1 : ℝ))))))))
  : ((1 /. 4) * V) = (((4 /. 15) * (a ^ (2 : ℕ))) * (Real.rpow (a * b) (((2 : ℝ))⁻¹))) := by
  sorry

theorem proof_gap_exercise_2467_7
  (S : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (V : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : V ∈ (Set.univ : Set ℝ))
  (h4 : a > 0)
  (h5 : b > 0)
  (h6 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = (∫ y in (0 : ℝ)..(Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)) * (1 : ℝ)))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ a)) → ((S x) = ((Real.rpow ((a * x) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x)) (((2 : ℝ))⁻¹)))))))
  (h8 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, ((S x_1) * (1 : ℝ)))))))
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = (∫ x_1 in (0 : ℝ)..a, (((Real.rpow ((a * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) * (Real.rpow (b * (a - x_1)) (((2 : ℝ))⁻¹))) * (1 : ℝ)))))))
  (h10 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((1 /. 4) * V) = ((Real.rpow (2 * b) (((2 : ℝ))⁻¹)) * (∫ x_1 in (0 : ℝ)..a, (((Real.rpow x_1 (((2 : ℝ))⁻¹)) * (a - x_1)) * (1 : ℝ))))))))
  (h11 : ((1 /. 4) * V) = (((4 /. 15) * (a ^ (2 : ℕ))) * (Real.rpow (a * b) (((2 : ℝ))⁻¹))))
  : V = (((16 /. 15) * (a ^ (2 : ℕ))) * (Real.rpow (a * b) (((2 : ℝ))⁻¹))) := by
  sorry
