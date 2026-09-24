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

-- exercise: exercise_4062

theorem proof_gap_exercise_4062_1
  (a : ℝ)
  (x : ℝ)
  (y : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ (p.1 ≥ 0) ∧ (p.2 ≥ 0) ∧ ((((p.1 - a) ^ (2 : ℕ)) + ((p.2 - a) ^ (2 : ℕ))) ≤ (a ^ (2 : ℕ))) ∧ (p.1 ≤ a)}))
  : I_x = (∫ x_1 in (0 : ℝ)..a, ((∫ y_1 in (0 : ℝ)..(a - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))), ((y_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4062_2
  (a : ℝ)
  (x : ℝ)
  (y : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ (p.1 ≥ 0) ∧ (p.2 ≥ 0) ∧ ((((p.1 - a) ^ (2 : ℕ)) + ((p.2 - a) ^ (2 : ℕ))) ≤ (a ^ (2 : ℕ))) ∧ (p.1 ≤ a)}))
  (h8 : I_x = (∫ x_1 in (0 : ℝ)..a, ((∫ y_1 in (0 : ℝ)..(a - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))), ((y_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))))
  : I_x = ((1 /. 3) * (∫ x_1 in (0 : ℝ)..a, (((((a ^ (3 : ℕ)) - (((3 : ℝ) * (a ^ (2 : ℕ))) * (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + (((3 : ℝ) * a) * ((((2 : ℝ) * a) * x_1) - (x_1 ^ (2 : ℕ))))) - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4062_3
  (a : ℝ)
  (x : ℝ)
  (y : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ (p.1 ≥ 0) ∧ (p.2 ≥ 0) ∧ ((((p.1 - a) ^ (2 : ℕ)) + ((p.2 - a) ^ (2 : ℕ))) ≤ (a ^ (2 : ℕ))) ∧ (p.1 ≤ a)}))
  (h8 : I_x = (∫ x_1 in (0 : ℝ)..a, ((∫ y_1 in (0 : ℝ)..(a - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))), ((y_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = ((1 /. 3) * (∫ x_1 in (0 : ℝ)..a, (((((a ^ (3 : ℕ)) - (((3 : ℝ) * (a ^ (2 : ℕ))) * (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + (((3 : ℝ) * a) * ((((2 : ℝ) * a) * x_1) - (x_1 ^ (2 : ℕ))))) - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2))) * (1 : ℝ)))))
  : (∫ x_1 in (0 : ℝ)..a, ((Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2)) * (1 : ℝ))) = (∫ t in (-(Real.pi /. 2))..(0 : ℝ), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4062_4
  (a : ℝ)
  (x : ℝ)
  (y : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ (p.1 ≥ 0) ∧ (p.2 ≥ 0) ∧ ((((p.1 - a) ^ (2 : ℕ)) + ((p.2 - a) ^ (2 : ℕ))) ≤ (a ^ (2 : ℕ))) ∧ (p.1 ≤ a)}))
  (h8 : I_x = (∫ x_1 in (0 : ℝ)..a, ((∫ y_1 in (0 : ℝ)..(a - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))), ((y_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = ((1 /. 3) * (∫ x_1 in (0 : ℝ)..a, (((((a ^ (3 : ℕ)) - (((3 : ℝ) * (a ^ (2 : ℕ))) * (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + (((3 : ℝ) * a) * ((((2 : ℝ) * a) * x_1) - (x_1 ^ (2 : ℕ))))) - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2))) * (1 : ℝ)))))
  (h10 : (∫ x_1 in (0 : ℝ)..a, ((Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2)) * (1 : ℝ))) = (∫ t in (-(Real.pi /. 2))..(0 : ℝ), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))))
  : I_x = (((a ^ (4 : ℕ)) * (1 - (Real.pi /. 4))) - ((1 /. 3) * (∫ t in (0 : ℝ)..(Real.pi /. 2), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_4062_5
  (a : ℝ)
  (x : ℝ)
  (y : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ (p.1 ≥ 0) ∧ (p.2 ≥ 0) ∧ ((((p.1 - a) ^ (2 : ℕ)) + ((p.2 - a) ^ (2 : ℕ))) ≤ (a ^ (2 : ℕ))) ∧ (p.1 ≤ a)}))
  (h8 : I_x = (∫ x_1 in (0 : ℝ)..a, ((∫ y_1 in (0 : ℝ)..(a - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))), ((y_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = ((1 /. 3) * (∫ x_1 in (0 : ℝ)..a, (((((a ^ (3 : ℕ)) - (((3 : ℝ) * (a ^ (2 : ℕ))) * (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + (((3 : ℝ) * a) * ((((2 : ℝ) * a) * x_1) - (x_1 ^ (2 : ℕ))))) - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2))) * (1 : ℝ)))))
  (h10 : (∫ x_1 in (0 : ℝ)..a, ((Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2)) * (1 : ℝ))) = (∫ t in (-(Real.pi /. 2))..(0 : ℝ), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))))
  (h11 : I_x = (((a ^ (4 : ℕ)) * (1 - (Real.pi /. 4))) - ((1 /. 3) * (∫ t in (0 : ℝ)..(Real.pi /. 2), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))))))
  : I_x = (((a ^ (4 : ℕ)) /. 16) * (16 - (5 * Real.pi))) := by
  sorry

theorem proof_gap_exercise_4062_6
  (a : ℝ)
  (x : ℝ)
  (y : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ (p.1 ≥ 0) ∧ (p.2 ≥ 0) ∧ ((((p.1 - a) ^ (2 : ℕ)) + ((p.2 - a) ^ (2 : ℕ))) ≤ (a ^ (2 : ℕ))) ∧ (p.1 ≤ a)}))
  (h8 : I_x = (∫ x_1 in (0 : ℝ)..a, ((∫ y_1 in (0 : ℝ)..(a - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))), ((y_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = ((1 /. 3) * (∫ x_1 in (0 : ℝ)..a, (((((a ^ (3 : ℕ)) - (((3 : ℝ) * (a ^ (2 : ℕ))) * (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + (((3 : ℝ) * a) * ((((2 : ℝ) * a) * x_1) - (x_1 ^ (2 : ℕ))))) - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2))) * (1 : ℝ)))))
  (h10 : (∫ x_1 in (0 : ℝ)..a, ((Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2)) * (1 : ℝ))) = (∫ t in (-(Real.pi /. 2))..(0 : ℝ), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))))
  (h11 : I_x = (((a ^ (4 : ℕ)) * (1 - (Real.pi /. 4))) - ((1 /. 3) * (∫ t in (0 : ℝ)..(Real.pi /. 2), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))))))
  (h12 : I_x = (((a ^ (4 : ℕ)) /. 16) * (16 - (5 * Real.pi))))
  : I_y = I_x := by
  sorry

theorem proof_gap_exercise_4062_7
  (a : ℝ)
  (x : ℝ)
  (y : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ (p.1 ≥ 0) ∧ (p.2 ≥ 0) ∧ ((((p.1 - a) ^ (2 : ℕ)) + ((p.2 - a) ^ (2 : ℕ))) ≤ (a ^ (2 : ℕ))) ∧ (p.1 ≤ a)}))
  (h8 : I_x = (∫ x_1 in (0 : ℝ)..a, ((∫ y_1 in (0 : ℝ)..(a - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))), ((y_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = ((1 /. 3) * (∫ x_1 in (0 : ℝ)..a, (((((a ^ (3 : ℕ)) - (((3 : ℝ) * (a ^ (2 : ℕ))) * (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) + (((3 : ℝ) * a) * ((((2 : ℝ) * a) * x_1) - (x_1 ^ (2 : ℕ))))) - (Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2))) * (1 : ℝ)))))
  (h10 : (∫ x_1 in (0 : ℝ)..a, ((Real.rpow (((2 * a) * x_1) - (x_1 ^ (2 : ℕ))) (3 /. 2)) * (1 : ℝ))) = (∫ t in (-(Real.pi /. 2))..(0 : ℝ), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))))
  (h11 : I_x = (((a ^ (4 : ℕ)) * (1 - (Real.pi /. 4))) - ((1 /. 3) * (∫ t in (0 : ℝ)..(Real.pi /. 2), (((a ^ (4 : ℕ)) * ((Real.cos t) ^ (4 : ℕ))) * (1 : ℝ))))))
  (h12 : I_x = (((a ^ (4 : ℕ)) /. 16) * (16 - (5 * Real.pi))))
  (h13 : I_y = I_x)
  : I_y = (((a ^ (4 : ℕ)) /. 16) * (16 - (5 * Real.pi))) := by
  sorry
