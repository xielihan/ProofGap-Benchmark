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

-- exercise: exercise_2274

theorem proof_gap_exercise_2274_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 3)) → ((((1 + x) > 0) ∧ (0 ≤ (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)) ≤ 1)))) := by
  sorry

theorem proof_gap_exercise_2274_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 3)) → ((((1 + x) > 0) ∧ (0 ≤ (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)) ≤ 1)))))
  : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (((3 * (Real.arcsin (Real.rpow (3 /. (1 + 3)) (((2 : ℝ))⁻¹)))) - (0 * (Real.arcsin (Real.rpow (0 /. (1 + 0)) (((2 : ℝ))⁻¹))))) - (∫ x in (0 : ℝ)..(3 : ℝ), (((Real.rpow x (((2 : ℝ))⁻¹)) /. ((2 : ℝ) * ((1 : ℝ) + x))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2274_3
  (x : ℝ)
  (h1 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 3)) → ((((1 + x_1) > 0) ∧ (0 ≤ (Real.rpow (x_1 /. (1 + x_1)) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow (x_1 /. (1 + x_1)) (((2 : ℝ))⁻¹)) ≤ 1)))))
  (h2 : (∫ x_1 in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x_1 /. (1 + x_1)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (((3 * (Real.arcsin (Real.rpow (3 /. (1 + 3)) (((2 : ℝ))⁻¹)))) - (0 * (Real.arcsin (Real.rpow (0 /. (1 + 0)) (((2 : ℝ))⁻¹))))) - (∫ x_1 in (0 : ℝ)..(3 : ℝ), (((Real.rpow x_1 (((2 : ℝ))⁻¹)) /. ((2 : ℝ) * ((1 : ℝ) + x_1))) * (1 : ℝ)))))
  (h3 : (Real.rpow x (((2 : ℝ))⁻¹)) = t)
  (h4 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 3)))
  : 0 ≤ t := by
  sorry

theorem proof_gap_exercise_2274_4
  (x : ℝ)
  (h1 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 ≤ 3)) → ((((1 + x_1) > 0) ∧ (0 ≤ (Real.rpow (x_1 /. (1 + x_1)) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow (x_1 /. (1 + x_1)) (((2 : ℝ))⁻¹)) ≤ 1)))))
  (h2 : (∫ x_1 in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x_1 /. (1 + x_1)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (((3 * (Real.arcsin (Real.rpow (3 /. (1 + 3)) (((2 : ℝ))⁻¹)))) - (0 * (Real.arcsin (Real.rpow (0 /. (1 + 0)) (((2 : ℝ))⁻¹))))) - (∫ x_1 in (0 : ℝ)..(3 : ℝ), (((Real.rpow x_1 (((2 : ℝ))⁻¹)) /. ((2 : ℝ) * ((1 : ℝ) + x_1))) * (1 : ℝ)))))
  (h3 : (Real.rpow x (((2 : ℝ))⁻¹)) = t)
  (h4 : 0 ≤ t)
  (h5 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 3)))
  : t ≤ (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)) := by
  sorry

theorem proof_gap_exercise_2274_5
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 3)) → ((((1 + x) > 0) ∧ (0 ≤ (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)) ≤ 1)))))
  (h2 : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (((3 * (Real.arcsin (Real.rpow (3 /. (1 + 3)) (((2 : ℝ))⁻¹)))) - (0 * (Real.arcsin (Real.rpow (0 /. (1 + 0)) (((2 : ℝ))⁻¹))))) - (∫ x in (0 : ℝ)..(3 : ℝ), (((Real.rpow x (((2 : ℝ))⁻¹)) /. ((2 : ℝ) * ((1 : ℝ) + x))) * (1 : ℝ)))))
  (h3 : (Real.rpow x (((2 : ℝ))⁻¹)) = t)
  (h4 : 0 ≤ t)
  (h5 : t ≤ (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)))
  : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi - (∫ t in (0 : ℝ)..(Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)), (((t ^ (2 : ℕ)) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2274_6
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 3)) → ((((1 + x) > 0) ∧ (0 ≤ (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)) ≤ 1)))))
  (h2 : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (((3 * (Real.arcsin (Real.rpow (3 /. (1 + 3)) (((2 : ℝ))⁻¹)))) - (0 * (Real.arcsin (Real.rpow (0 /. (1 + 0)) (((2 : ℝ))⁻¹))))) - (∫ x in (0 : ℝ)..(3 : ℝ), (((Real.rpow x (((2 : ℝ))⁻¹)) /. ((2 : ℝ) * ((1 : ℝ) + x))) * (1 : ℝ)))))
  (h3 : (Real.rpow x (((2 : ℝ))⁻¹)) = t)
  (h4 : 0 ≤ t)
  (h5 : t ≤ (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)))
  (h6 : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi - (∫ t in (0 : ℝ)..(Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)), (((t ^ (2 : ℕ)) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ)))))
  : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi - (((Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)) - (Real.arctan (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)))) - (0 - (Real.arctan (0 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_2274_7
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x)) ∧ (x ≤ 3)) → ((((1 + x) > 0) ∧ (0 ≤ (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹)) ≤ 1)))))
  (h2 : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (((3 * (Real.arcsin (Real.rpow (3 /. (1 + 3)) (((2 : ℝ))⁻¹)))) - (0 * (Real.arcsin (Real.rpow (0 /. (1 + 0)) (((2 : ℝ))⁻¹))))) - (∫ x in (0 : ℝ)..(3 : ℝ), (((Real.rpow x (((2 : ℝ))⁻¹)) /. ((2 : ℝ) * ((1 : ℝ) + x))) * (1 : ℝ)))))
  (h3 : (Real.rpow x (((2 : ℝ))⁻¹)) = t)
  (h4 : 0 ≤ t)
  (h5 : t ≤ (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)))
  (h6 : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi - (∫ t in (0 : ℝ)..(Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)), (((t ^ (2 : ℕ)) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ)))))
  (h7 : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi - (((Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)) - (Real.arctan (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹)))) - (0 - (Real.arctan (0 : ℝ))))))
  : (∫ x in (0 : ℝ)..(3 : ℝ), ((Real.arcsin (Real.rpow (x /. (1 + x)) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (((4 * Real.pi) /. 3) - (Real.rpow (3 : ℝ) (((2 : ℝ))⁻¹))) := by
  sorry
