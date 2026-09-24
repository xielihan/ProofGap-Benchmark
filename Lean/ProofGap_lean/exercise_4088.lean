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

-- exercise: exercise_4088

theorem proof_gap_exercise_4088_1
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (v_uCF_u88 : ℝ)
  (I : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : r ∈ (Set.univ : Set ℝ))
  (h6 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h7 : v_uCF_u88 ∈ (Set.univ : Set ℝ))
  (h8 : I ∈ (Set.univ : Set ℝ))
  (h9 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ 1)) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.rpow (1 - (p.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.rpow ((2 - (p.1 ^ (2 : ℕ))) - (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))}))
  (h10 : x = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h11 : y = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h12 : z = (r * (Real.sin v_uCF_u88)))
  : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ ((Real.pi /. 4) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))}) := by
  sorry

theorem proof_gap_exercise_4088_2
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (v_uCF_u88 : ℝ)
  (I : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : r ∈ (Set.univ : Set ℝ))
  (h6 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h7 : v_uCF_u88 ∈ (Set.univ : Set ℝ))
  (h8 : I ∈ (Set.univ : Set ℝ))
  (h9 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ 1)) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.rpow (1 - (p.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.rpow ((2 - (p.1 ^ (2 : ℕ))) - (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))}))
  (h10 : x = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h11 : y = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h12 : z = (r * (Real.sin v_uCF_u88)))
  (h13 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ ((Real.pi /. 4) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))}))
  : |(I)| = ((r ^ (2 : ℕ)) * (Real.cos v_uCF_u88)) := by
  sorry

theorem proof_gap_exercise_4088_3
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (v_uCF_u88 : ℝ)
  (I : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : r ∈ (Set.univ : Set ℝ))
  (h6 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h7 : v_uCF_u88 ∈ (Set.univ : Set ℝ))
  (h8 : I ∈ (Set.univ : Set ℝ))
  (h9 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ 1)) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.rpow (1 - (p.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.rpow ((2 - (p.1 ^ (2 : ℕ))) - (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))}))
  (h10 : x = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h11 : y = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h12 : z = (r * (Real.sin v_uCF_u88)))
  (h13 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ ((Real.pi /. 4) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))}))
  (h14 : |(I)| = ((r ^ (2 : ℕ)) * (Real.cos v_uCF_u88)))
  : (∫ x_1 in (0 : ℝ)..(1 : ℝ), ((∫ y_1 in (0 : ℝ)..(Real.rpow (1 - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((∫ z_1 in (Real.rpow ((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))..(Real.rpow ((2 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((z_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCF_u86_1 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), ((∫ r_1 in (0 : ℝ)..(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)), (((((r_1 ^ (2 : ℕ)) * (Real.cos v_uCF_u88_1)) * (r_1 ^ (2 : ℕ))) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4088_4
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (v_uCF_u88 : ℝ)
  (I : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : r ∈ (Set.univ : Set ℝ))
  (h6 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h7 : v_uCF_u88 ∈ (Set.univ : Set ℝ))
  (h8 : I ∈ (Set.univ : Set ℝ))
  (h9 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ 1)) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.rpow (1 - (p.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.rpow ((2 - (p.1 ^ (2 : ℕ))) - (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))}))
  (h10 : x = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h11 : y = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h12 : z = (r * (Real.sin v_uCF_u88)))
  (h13 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ ((Real.pi /. 4) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))}))
  (h14 : |(I)| = ((r ^ (2 : ℕ)) * (Real.cos v_uCF_u88)))
  (h15 : (∫ x_1 in (0 : ℝ)..(1 : ℝ), ((∫ y_1 in (0 : ℝ)..(Real.rpow (1 - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((∫ z_1 in (Real.rpow ((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))..(Real.rpow ((2 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((z_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCF_u86_1 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), ((∫ r_1 in (0 : ℝ)..(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)), (((((r_1 ^ (2 : ℕ)) * (Real.cos v_uCF_u88_1)) * (r_1 ^ (2 : ℕ))) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))))
  : (∫ v_uCF_u86_1 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), ((∫ r_1 in (0 : ℝ)..(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)), (((((r_1 ^ (2 : ℕ)) * (Real.cos v_uCF_u88_1)) * (r_1 ^ (2 : ℕ))) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = ((((4 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) /. 5) * (Real.pi /. 2)) * (∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), (((Real.cos v_uCF_u88_1) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4088_5
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (v_uCF_u88 : ℝ)
  (I : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : r ∈ (Set.univ : Set ℝ))
  (h6 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h7 : v_uCF_u88 ∈ (Set.univ : Set ℝ))
  (h8 : I ∈ (Set.univ : Set ℝ))
  (h9 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ 1)) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.rpow (1 - (p.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.rpow ((2 - (p.1 ^ (2 : ℕ))) - (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))}))
  (h10 : x = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h11 : y = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h12 : z = (r * (Real.sin v_uCF_u88)))
  (h13 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ ((Real.pi /. 4) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))}))
  (h14 : |(I)| = ((r ^ (2 : ℕ)) * (Real.cos v_uCF_u88)))
  (h15 : (∫ x_1 in (0 : ℝ)..(1 : ℝ), ((∫ y_1 in (0 : ℝ)..(Real.rpow (1 - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((∫ z_1 in (Real.rpow ((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))..(Real.rpow ((2 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((z_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCF_u86_1 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), ((∫ r_1 in (0 : ℝ)..(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)), (((((r_1 ^ (2 : ℕ)) * (Real.cos v_uCF_u88_1)) * (r_1 ^ (2 : ℕ))) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))))
  (h16 : (∫ v_uCF_u86_1 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), ((∫ r_1 in (0 : ℝ)..(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)), (((((r_1 ^ (2 : ℕ)) * (Real.cos v_uCF_u88_1)) * (r_1 ^ (2 : ℕ))) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = ((((4 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) /. 5) * (Real.pi /. 2)) * (∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), (((Real.cos v_uCF_u88_1) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  : ((((4 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) /. 5) * (Real.pi /. 2)) * (∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), (((Real.cos v_uCF_u88_1) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ)))) = ((Real.pi /. 15) * ((2 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) - 1)) := by
  sorry

theorem proof_gap_exercise_4088_6
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (v_uCF_u88 : ℝ)
  (I : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : z ∈ (Set.univ : Set ℝ))
  (h5 : r ∈ (Set.univ : Set ℝ))
  (h6 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h7 : v_uCF_u88 ∈ (Set.univ : Set ℝ))
  (h8 : I ∈ (Set.univ : Set ℝ))
  (h9 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ 1)) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.rpow (1 - (p.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))) ∧ ((Real.rpow ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.rpow ((2 - (p.1 ^ (2 : ℕ))) - (p.2.1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))}))
  (h10 : x = ((r * (Real.cos v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h11 : y = ((r * (Real.sin v_uCF_u86)) * (Real.cos v_uCF_u88)))
  (h12 : z = (r * (Real.sin v_uCF_u88)))
  (h13 : V = ({p : ℝ × (ℝ × ℝ) | (((((((((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (0 ≤ p.2.1)) ∧ (p.2.1 ≤ (Real.pi /. 2))) ∧ ((Real.pi /. 4) ≤ p.2.2)) ∧ (p.2.2 ≤ (Real.pi /. 2))) ∧ (0 ≤ p.1)) ∧ (p.1 ≤ (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))))}))
  (h14 : |(I)| = ((r ^ (2 : ℕ)) * (Real.cos v_uCF_u88)))
  (h15 : (∫ x_1 in (0 : ℝ)..(1 : ℝ), ((∫ y_1 in (0 : ℝ)..(Real.rpow (1 - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((∫ z_1 in (Real.rpow ((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))..(Real.rpow ((2 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((z_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = (∫ v_uCF_u86_1 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), ((∫ r_1 in (0 : ℝ)..(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)), (((((r_1 ^ (2 : ℕ)) * (Real.cos v_uCF_u88_1)) * (r_1 ^ (2 : ℕ))) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))))
  (h16 : (∫ v_uCF_u86_1 in (0 : ℝ)..(Real.pi /. 2), ((∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), ((∫ r_1 in (0 : ℝ)..(Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)), (((((r_1 ^ (2 : ℕ)) * (Real.cos v_uCF_u88_1)) * (r_1 ^ (2 : ℕ))) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = ((((4 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) /. 5) * (Real.pi /. 2)) * (∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), (((Real.cos v_uCF_u88_1) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h17 : ((((4 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) /. 5) * (Real.pi /. 2)) * (∫ v_uCF_u88_1 in (Real.pi /. 4)..(Real.pi /. 2), (((Real.cos v_uCF_u88_1) * ((Real.sin v_uCF_u88_1) ^ (2 : ℕ))) * (1 : ℝ)))) = ((Real.pi /. 15) * ((2 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) - 1)))
  : (∫ x_1 in (0 : ℝ)..(1 : ℝ), ((∫ y_1 in (0 : ℝ)..(Real.rpow (1 - (x_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((∫ z_1 in (Real.rpow ((x_1 ^ (2 : ℕ)) + (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹))..(Real.rpow ((2 - (x_1 ^ (2 : ℕ))) - (y_1 ^ (2 : ℕ))) (((2 : ℝ))⁻¹)), ((z_1 ^ (2 : ℕ)) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) = ((Real.pi /. 15) * ((2 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹))) - 1)) := by
  sorry
