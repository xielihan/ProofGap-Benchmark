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

-- exercise: exercise_4063

theorem proof_gap_exercise_4063_1
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (a : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : r ∈ (Set.univ : Set ℝ))
  (h2 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) ≤ p.2) ∧ (p.2 ≤ Real.pi) ∧ (0 ≤ p.1) ∧ (p.1 ≤ (a * (1 + (Real.cos p.2))))}))
  : I_x = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4063_2
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (a : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : r ∈ (Set.univ : Set ℝ))
  (h2 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) ≤ p.2) ∧ (p.2 ≤ Real.pi) ∧ (0 ≤ p.1) ∧ (p.1 ≤ (a * (1 + (Real.cos p.2))))}))
  (h8 : I_x = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  : I_x = (((1 /. 4) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4063_3
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (a : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : r ∈ (Set.univ : Set ℝ))
  (h2 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) ≤ p.2) ∧ (p.2 ≤ Real.pi) ∧ (0 ≤ p.1) ∧ (p.1 ≤ (a * (1 + (Real.cos p.2))))}))
  (h8 : I_x = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = (((1 /. 4) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  : I_x = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, (((((((1 : ℝ) + ((4 : ℝ) * (Real.cos v_uCF_u86_1))) + ((6 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ)))) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (3 : ℕ)))) + ((Real.cos v_uCF_u86_1) ^ (4 : ℕ))) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4063_4
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (a : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : r ∈ (Set.univ : Set ℝ))
  (h2 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) ≤ p.2) ∧ (p.2 ≤ Real.pi) ∧ (0 ≤ p.1) ∧ (p.1 ≤ (a * (1 + (Real.cos p.2))))}))
  (h8 : I_x = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = (((1 /. 4) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h10 : I_x = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, (((((((1 : ℝ) + ((4 : ℝ) * (Real.cos v_uCF_u86_1))) + ((6 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ)))) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (3 : ℕ)))) + ((Real.cos v_uCF_u86_1) ^ (4 : ℕ))) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  : I_x = (((21 /. 32) * Real.pi) * (a ^ (4 : ℕ))) := by
  sorry

theorem proof_gap_exercise_4063_5
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (a : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : r ∈ (Set.univ : Set ℝ))
  (h2 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) ≤ p.2) ∧ (p.2 ≤ Real.pi) ∧ (0 ≤ p.1) ∧ (p.1 ≤ (a * (1 + (Real.cos p.2))))}))
  (h8 : I_x = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = (((1 /. 4) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h10 : I_x = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, (((((((1 : ℝ) + ((4 : ℝ) * (Real.cos v_uCF_u86_1))) + ((6 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ)))) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (3 : ℕ)))) + ((Real.cos v_uCF_u86_1) ^ (4 : ℕ))) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h11 : I_x = (((21 /. 32) * Real.pi) * (a ^ (4 : ℕ))))
  : I_y = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4063_6
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (a : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : r ∈ (Set.univ : Set ℝ))
  (h2 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) ≤ p.2) ∧ (p.2 ≤ Real.pi) ∧ (0 ≤ p.1) ∧ (p.1 ≤ (a * (1 + (Real.cos p.2))))}))
  (h8 : I_x = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = (((1 /. 4) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h10 : I_x = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, (((((((1 : ℝ) + ((4 : ℝ) * (Real.cos v_uCF_u86_1))) + ((6 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ)))) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (3 : ℕ)))) + ((Real.cos v_uCF_u86_1) ^ (4 : ℕ))) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h11 : I_x = (((21 /. 32) * Real.pi) * (a ^ (4 : ℕ))))
  (h12 : I_y = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  : I_y = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4063_7
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (a : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : r ∈ (Set.univ : Set ℝ))
  (h2 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) ≤ p.2) ∧ (p.2 ≤ Real.pi) ∧ (0 ≤ p.1) ∧ (p.1 ≤ (a * (1 + (Real.cos p.2))))}))
  (h8 : I_x = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = (((1 /. 4) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h10 : I_x = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, (((((((1 : ℝ) + ((4 : ℝ) * (Real.cos v_uCF_u86_1))) + ((6 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ)))) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (3 : ℕ)))) + ((Real.cos v_uCF_u86_1) ^ (4 : ℕ))) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h11 : I_x = (((21 /. 32) * Real.pi) * (a ^ (4 : ℕ))))
  (h12 : I_y = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  (h13 : I_y = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  : I_y = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, (((((((Real.cos v_uCF_u86_1) ^ (2 : ℕ)) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (3 : ℕ)))) + ((6 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (4 : ℕ)))) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (5 : ℕ)))) + ((Real.cos v_uCF_u86_1) ^ (6 : ℕ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_4063_8
  (r : ℝ)
  (v_uCF_u86 : ℝ)
  (a : ℝ)
  (I_x : ℝ)
  (I_y : ℝ)
  (h1 : r ∈ (Set.univ : Set ℝ))
  (h2 : v_uCF_u86 ∈ (Set.univ : Set ℝ))
  (h3 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h4 : I_x ∈ (Set.univ : Set ℝ))
  (h5 : I_y ∈ (Set.univ : Set ℝ))
  (h6 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h7 : D = ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((-Real.pi) ≤ p.2) ∧ (p.2 ≤ Real.pi) ∧ (0 ≤ p.1) ∧ (p.1 ≤ (a * (1 + (Real.cos p.2))))}))
  (h8 : I_x = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  (h9 : I_x = (((1 /. 4) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h10 : I_x = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, (((((((1 : ℝ) + ((4 : ℝ) * (Real.cos v_uCF_u86_1))) + ((6 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ)))) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (3 : ℕ)))) + ((Real.cos v_uCF_u86_1) ^ (4 : ℕ))) * ((Real.sin v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h11 : I_x = (((21 /. 32) * Real.pi) * (a ^ (4 : ℕ))))
  (h12 : I_y = (∫ v_uCF_u86_1 in (-Real.pi)..Real.pi, ((∫ r_1 in (0 : ℝ)..(a * (1 + (Real.cos v_uCF_u86_1))), ((((r_1 ^ (2 : ℕ)) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ))) * r_1) * (1 : ℝ))) * (1 : ℝ))))
  (h13 : I_y = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, ((((1 + (Real.cos v_uCF_u86_1)) ^ (4 : ℕ)) * ((Real.cos v_uCF_u86_1) ^ (2 : ℕ))) * (1 : ℝ)))))
  (h14 : I_y = (((1 /. 2) * (a ^ (4 : ℕ))) * (∫ v_uCF_u86_1 in (0 : ℝ)..Real.pi, (((((((Real.cos v_uCF_u86_1) ^ (2 : ℕ)) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (3 : ℕ)))) + ((6 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (4 : ℕ)))) + ((4 : ℝ) * ((Real.cos v_uCF_u86_1) ^ (5 : ℕ)))) + ((Real.cos v_uCF_u86_1) ^ (6 : ℕ))) * (1 : ℝ)))))
  : I_y = (((49 /. 32) * Real.pi) * (a ^ (4 : ℕ))) := by
  sorry
