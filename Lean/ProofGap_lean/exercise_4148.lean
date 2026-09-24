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

-- exercise: exercise_4148

theorem proof_gap_exercise_4148_1
  (I_z : ℝ)
  (I_zx : ℝ)
  (I_zy : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (u : ℝ)
  (v : ℝ)
  (J : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : I_z ∈ (Set.univ : Set ℝ))
  (h3 : I_zx ∈ (Set.univ : Set ℝ))
  (h4 : I_zy ∈ (Set.univ : Set ℝ))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : (z ∈ (Set.univ : Set ℝ)) ∧ (z ≥ 0))
  (h8 : ((u ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ u)) ∧ (u ≤ 1))
  (h9 : ((v ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ v)) ∧ (v ≤ 1))
  (h10 : J ∈ (Set.univ : Set ℝ))
  (h11 : V = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ≥ 0) ∧ (p.2.2 ≤ ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))) ∧ (((-(1 : ℝ)) ≤ (p.1 + p.2.1)) ∧ ((p.1 + p.2.1) ≤ 1)) ∧ (((-(1 : ℝ)) ≤ (p.1 - p.2.1)) ∧ ((p.1 - p.2.1) ≤ 1))}))
  : I_z = (I_zx + I_zy) := by
  sorry

theorem proof_gap_exercise_4148_2
  (I_z : ℝ)
  (I_zx : ℝ)
  (I_zy : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (u : ℝ)
  (v : ℝ)
  (J : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : I_z ∈ (Set.univ : Set ℝ))
  (h3 : I_zx ∈ (Set.univ : Set ℝ))
  (h4 : I_zy ∈ (Set.univ : Set ℝ))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : (z ∈ (Set.univ : Set ℝ)) ∧ (z ≥ 0))
  (h8 : ((u ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ u)) ∧ (u ≤ 1))
  (h9 : ((v ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ v)) ∧ (v ≤ 1))
  (h10 : J ∈ (Set.univ : Set ℝ))
  (h11 : V = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ≥ 0) ∧ (p.2.2 ≤ ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))) ∧ (((-(1 : ℝ)) ≤ (p.1 + p.2.1)) ∧ ((p.1 + p.2.1) ≤ 1)) ∧ (((-(1 : ℝ)) ≤ (p.1 - p.2.1)) ∧ ((p.1 - p.2.1) ≤ 1))}))
  (h12 : I_z = (I_zx + I_zy))
  (h13 : x = ((u + v) /. 2))
  (h14 : y = ((u - v) /. 2))
  : (x + y) = u := by
  sorry

theorem proof_gap_exercise_4148_3
  (I_z : ℝ)
  (I_zx : ℝ)
  (I_zy : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (u : ℝ)
  (v : ℝ)
  (J : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : I_z ∈ (Set.univ : Set ℝ))
  (h3 : I_zx ∈ (Set.univ : Set ℝ))
  (h4 : I_zy ∈ (Set.univ : Set ℝ))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : (z ∈ (Set.univ : Set ℝ)) ∧ (z ≥ 0))
  (h8 : ((u ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ u)) ∧ (u ≤ 1))
  (h9 : ((v ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ v)) ∧ (v ≤ 1))
  (h10 : J ∈ (Set.univ : Set ℝ))
  (h11 : V = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ≥ 0) ∧ (p.2.2 ≤ ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))) ∧ (((-(1 : ℝ)) ≤ (p.1 + p.2.1)) ∧ ((p.1 + p.2.1) ≤ 1)) ∧ (((-(1 : ℝ)) ≤ (p.1 - p.2.1)) ∧ ((p.1 - p.2.1) ≤ 1))}))
  (h12 : I_z = (I_zx + I_zy))
  (h13 : x = ((u + v) /. 2))
  (h14 : y = ((u - v) /. 2))
  (h15 : (x + y) = u)
  : (x - y) = v := by
  sorry

theorem proof_gap_exercise_4148_4
  (I_z : ℝ)
  (I_zx : ℝ)
  (I_zy : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (u : ℝ)
  (v : ℝ)
  (J : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : I_z ∈ (Set.univ : Set ℝ))
  (h3 : I_zx ∈ (Set.univ : Set ℝ))
  (h4 : I_zy ∈ (Set.univ : Set ℝ))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : (z ∈ (Set.univ : Set ℝ)) ∧ (z ≥ 0))
  (h8 : ((u ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ u)) ∧ (u ≤ 1))
  (h9 : ((v ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ v)) ∧ (v ≤ 1))
  (h10 : J ∈ (Set.univ : Set ℝ))
  (h11 : V = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ≥ 0) ∧ (p.2.2 ≤ ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))) ∧ (((-(1 : ℝ)) ≤ (p.1 + p.2.1)) ∧ ((p.1 + p.2.1) ≤ 1)) ∧ (((-(1 : ℝ)) ≤ (p.1 - p.2.1)) ∧ ((p.1 - p.2.1) ≤ 1))}))
  (h12 : I_z = (I_zx + I_zy))
  (h13 : x = ((u + v) /. 2))
  (h14 : y = ((u - v) /. 2))
  (h15 : (x + y) = u)
  (h16 : (x - y) = v)
  : z = (((u ^ (2 : ℕ)) + (v ^ (2 : ℕ))) /. 2) := by
  sorry

theorem proof_gap_exercise_4148_5
  (I_z : ℝ)
  (I_zx : ℝ)
  (I_zy : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (u : ℝ)
  (v : ℝ)
  (J : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : I_z ∈ (Set.univ : Set ℝ))
  (h3 : I_zx ∈ (Set.univ : Set ℝ))
  (h4 : I_zy ∈ (Set.univ : Set ℝ))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : (z ∈ (Set.univ : Set ℝ)) ∧ (z ≥ 0))
  (h8 : ((u ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ u)) ∧ (u ≤ 1))
  (h9 : ((v ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ v)) ∧ (v ≤ 1))
  (h10 : J ∈ (Set.univ : Set ℝ))
  (h11 : V = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ≥ 0) ∧ (p.2.2 ≤ ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))) ∧ (((-(1 : ℝ)) ≤ (p.1 + p.2.1)) ∧ ((p.1 + p.2.1) ≤ 1)) ∧ (((-(1 : ℝ)) ≤ (p.1 - p.2.1)) ∧ ((p.1 - p.2.1) ≤ 1))}))
  (h12 : I_z = (I_zx + I_zy))
  (h13 : x = ((u + v) /. 2))
  (h14 : y = ((u - v) /. 2))
  (h15 : (x + y) = u)
  (h16 : (x - y) = v)
  (h17 : z = (((u ^ (2 : ℕ)) + (v ^ (2 : ℕ))) /. 2))
  : |(J)| = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_4148_6
  (I_z : ℝ)
  (I_zx : ℝ)
  (I_zy : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (u : ℝ)
  (v : ℝ)
  (J : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : I_z ∈ (Set.univ : Set ℝ))
  (h3 : I_zx ∈ (Set.univ : Set ℝ))
  (h4 : I_zy ∈ (Set.univ : Set ℝ))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : (z ∈ (Set.univ : Set ℝ)) ∧ (z ≥ 0))
  (h8 : ((u ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ u)) ∧ (u ≤ 1))
  (h9 : ((v ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ v)) ∧ (v ≤ 1))
  (h10 : J ∈ (Set.univ : Set ℝ))
  (h11 : V = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ≥ 0) ∧ (p.2.2 ≤ ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))) ∧ (((-(1 : ℝ)) ≤ (p.1 + p.2.1)) ∧ ((p.1 + p.2.1) ≤ 1)) ∧ (((-(1 : ℝ)) ≤ (p.1 - p.2.1)) ∧ ((p.1 - p.2.1) ≤ 1))}))
  (h12 : I_z = (I_zx + I_zy))
  (h13 : x = ((u + v) /. 2))
  (h14 : y = ((u - v) /. 2))
  (h15 : (x + y) = u)
  (h16 : (x - y) = v)
  (h17 : z = (((u ^ (2 : ℕ)) + (v ^ (2 : ℕ))) /. 2))
  (h18 : |(J)| = (1 /. 2))
  : I_z = (∫ u_1 in (-(1 : ℝ))..(1 : ℝ), ((∫ v_1 in (-(1 : ℝ))..(1 : ℝ), ((∫ z_1 in (0 : ℝ)..(((u_1 ^ (2 : ℕ)) + (v_1 ^ (2 : ℕ))) /. 2), ((((1 : ℝ) /. (2 : ℝ)) * ((((u_1 - v_1) /. 2) ^ (2 : ℕ)) + (((u_1 + v_1) /. 2) ^ (2 : ℕ)))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4148_7
  (I_z : ℝ)
  (I_zx : ℝ)
  (I_zy : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (u : ℝ)
  (v : ℝ)
  (J : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : I_z ∈ (Set.univ : Set ℝ))
  (h3 : I_zx ∈ (Set.univ : Set ℝ))
  (h4 : I_zy ∈ (Set.univ : Set ℝ))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : (z ∈ (Set.univ : Set ℝ)) ∧ (z ≥ 0))
  (h8 : ((u ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ u)) ∧ (u ≤ 1))
  (h9 : ((v ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ v)) ∧ (v ≤ 1))
  (h10 : J ∈ (Set.univ : Set ℝ))
  (h11 : V = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ≥ 0) ∧ (p.2.2 ≤ ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))) ∧ (((-(1 : ℝ)) ≤ (p.1 + p.2.1)) ∧ ((p.1 + p.2.1) ≤ 1)) ∧ (((-(1 : ℝ)) ≤ (p.1 - p.2.1)) ∧ ((p.1 - p.2.1) ≤ 1))}))
  (h12 : I_z = (I_zx + I_zy))
  (h13 : x = ((u + v) /. 2))
  (h14 : y = ((u - v) /. 2))
  (h15 : (x + y) = u)
  (h16 : (x - y) = v)
  (h17 : z = (((u ^ (2 : ℕ)) + (v ^ (2 : ℕ))) /. 2))
  (h18 : |(J)| = (1 /. 2))
  (h19 : I_z = (∫ u_1 in (-(1 : ℝ))..(1 : ℝ), ((∫ v_1 in (-(1 : ℝ))..(1 : ℝ), ((∫ z_1 in (0 : ℝ)..(((u_1 ^ (2 : ℕ)) + (v_1 ^ (2 : ℕ))) /. 2), ((((1 : ℝ) /. (2 : ℝ)) * ((((u_1 - v_1) /. 2) ^ (2 : ℕ)) + (((u_1 + v_1) /. 2) ^ (2 : ℕ)))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))))
  : I_z = (∫ u_1 in (-(1 : ℝ))..(1 : ℝ), ((∫ v_1 in (-(1 : ℝ))..(1 : ℝ), (((((u_1 ^ (2 : ℕ)) + (v_1 ^ (2 : ℕ))) ^ (2 : ℕ)) /. (8 : ℝ)) * (1 : ℝ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4148_8
  (I_z : ℝ)
  (I_zx : ℝ)
  (I_zy : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (u : ℝ)
  (v : ℝ)
  (J : ℝ)
  (h1 : V ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h2 : I_z ∈ (Set.univ : Set ℝ))
  (h3 : I_zx ∈ (Set.univ : Set ℝ))
  (h4 : I_zy ∈ (Set.univ : Set ℝ))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : (z ∈ (Set.univ : Set ℝ)) ∧ (z ≥ 0))
  (h8 : ((u ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ u)) ∧ (u ≤ 1))
  (h9 : ((v ∈ (Set.univ : Set ℝ)) ∧ ((-(1 : ℝ)) ≤ v)) ∧ (v ≤ 1))
  (h10 : J ∈ (Set.univ : Set ℝ))
  (h11 : V = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ≥ 0) ∧ (p.2.2 ≤ ((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ)))) ∧ (((-(1 : ℝ)) ≤ (p.1 + p.2.1)) ∧ ((p.1 + p.2.1) ≤ 1)) ∧ (((-(1 : ℝ)) ≤ (p.1 - p.2.1)) ∧ ((p.1 - p.2.1) ≤ 1))}))
  (h12 : I_z = (I_zx + I_zy))
  (h13 : x = ((u + v) /. 2))
  (h14 : y = ((u - v) /. 2))
  (h15 : (x + y) = u)
  (h16 : (x - y) = v)
  (h17 : z = (((u ^ (2 : ℕ)) + (v ^ (2 : ℕ))) /. 2))
  (h18 : |(J)| = (1 /. 2))
  (h19 : I_z = (∫ u_1 in (-(1 : ℝ))..(1 : ℝ), ((∫ v_1 in (-(1 : ℝ))..(1 : ℝ), ((∫ z_1 in (0 : ℝ)..(((u_1 ^ (2 : ℕ)) + (v_1 ^ (2 : ℕ))) /. 2), ((((1 : ℝ) /. (2 : ℝ)) * ((((u_1 - v_1) /. 2) ^ (2 : ℕ)) + (((u_1 + v_1) /. 2) ^ (2 : ℕ)))) * (1 : ℝ))) * (1 : ℝ))) * (1 : ℝ))))
  (h20 : I_z = (∫ u_1 in (-(1 : ℝ))..(1 : ℝ), ((∫ v_1 in (-(1 : ℝ))..(1 : ℝ), (((((u_1 ^ (2 : ℕ)) + (v_1 ^ (2 : ℕ))) ^ (2 : ℕ)) /. (8 : ℝ)) * (1 : ℝ))) * (1 : ℝ))))
  : I_z = (14 /. 45) := by
  sorry
