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

-- exercise: exercise_3579

theorem proof_gap_exercise_3579_1
  (x_0 : ℝ)
  (y_0 : ℝ)
  (z_0 : ℝ)
  (R : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : y_0 ∈ (Set.univ : Set ℝ))
  (h3 : z_0 ∈ (Set.univ : Set ℝ))
  (h4 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h5 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h6 : x ∈ (Set.univ : Set ℝ))
  (h7 : y ∈ (Set.univ : Set ℝ))
  (h8 : z ∈ (Set.univ : Set ℝ))
  (h9 : (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) + (z_0 ^ (2 : ℕ))) > (R ^ (2 : ℕ)))
  (h10 : l_0 = (x_0, y_0, z_0))
  (h11 : r = (x, y, z))
  : ((((x - x_0) ^ (2 : ℕ)) + ((y - y_0) ^ (2 : ℕ))) + ((z - z_0) ^ (2 : ℕ))) ≤ (R ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_3579_2
  (x_0 : ℝ)
  (y_0 : ℝ)
  (z_0 : ℝ)
  (R : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : y_0 ∈ (Set.univ : Set ℝ))
  (h3 : z_0 ∈ (Set.univ : Set ℝ))
  (h4 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h5 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h6 : x ∈ (Set.univ : Set ℝ))
  (h7 : y ∈ (Set.univ : Set ℝ))
  (h8 : z ∈ (Set.univ : Set ℝ))
  (h9 : (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) + (z_0 ^ (2 : ℕ))) > (R ^ (2 : ℕ)))
  (h10 : l_0 = (x_0, y_0, z_0))
  (h11 : r = (x, y, z))
  (h12 : ((((x - x_0) ^ (2 : ℕ)) + ((y - y_0) ^ (2 : ℕ))) + ((z - z_0) ^ (2 : ℕ))) ≤ (R ^ (2 : ℕ)))
  : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) = ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3579_3
  (x_0 : ℝ)
  (y_0 : ℝ)
  (z_0 : ℝ)
  (R : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : y_0 ∈ (Set.univ : Set ℝ))
  (h3 : z_0 ∈ (Set.univ : Set ℝ))
  (h4 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h5 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h6 : x ∈ (Set.univ : Set ℝ))
  (h7 : y ∈ (Set.univ : Set ℝ))
  (h8 : z ∈ (Set.univ : Set ℝ))
  (h9 : (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) + (z_0 ^ (2 : ℕ))) > (R ^ (2 : ℕ)))
  (h10 : l_0 = (x_0, y_0, z_0))
  (h11 : r = (x, y, z))
  (h12 : ((((x - x_0) ^ (2 : ℕ)) + ((y - y_0) ^ (2 : ℕ))) + ((z - z_0) ^ (2 : ℕ))) ≤ (R ^ (2 : ℕ)))
  (h13 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) = ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) ≤ ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3579_4
  (x_0 : ℝ)
  (y_0 : ℝ)
  (z_0 : ℝ)
  (R : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : y_0 ∈ (Set.univ : Set ℝ))
  (h3 : z_0 ∈ (Set.univ : Set ℝ))
  (h4 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h5 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h6 : x ∈ (Set.univ : Set ℝ))
  (h7 : y ∈ (Set.univ : Set ℝ))
  (h8 : z ∈ (Set.univ : Set ℝ))
  (h9 : (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) + (z_0 ^ (2 : ℕ))) > (R ^ (2 : ℕ)))
  (h10 : l_0 = (x_0, y_0, z_0))
  (h11 : r = (x, y, z))
  (h12 : ((((x - x_0) ^ (2 : ℕ)) + ((y - y_0) ^ (2 : ℕ))) + ((z - z_0) ^ (2 : ℕ))) ≤ (R ^ (2 : ℕ)))
  (h13 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) = ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  (h14 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) ≤ ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) ≤ ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3579_5
  (x_0 : ℝ)
  (y_0 : ℝ)
  (z_0 : ℝ)
  (R : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : y_0 ∈ (Set.univ : Set ℝ))
  (h3 : z_0 ∈ (Set.univ : Set ℝ))
  (h4 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h5 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h6 : x ∈ (Set.univ : Set ℝ))
  (h7 : y ∈ (Set.univ : Set ℝ))
  (h8 : z ∈ (Set.univ : Set ℝ))
  (h9 : (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) + (z_0 ^ (2 : ℕ))) > (R ^ (2 : ℕ)))
  (h10 : l_0 = (x_0, y_0, z_0))
  (h11 : r = (x, y, z))
  (h12 : ((((x - x_0) ^ (2 : ℕ)) + ((y - y_0) ^ (2 : ℕ))) + ((z - z_0) ^ (2 : ℕ))) ≤ (R ^ (2 : ℕ)))
  (h13 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) = ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  (h14 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) ≤ ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  (h15 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) ≤ ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  : (((((((((y_0 ^ (2 : ℕ)) + (z_0 ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + (((x_0 ^ (2 : ℕ)) + (z_0 ^ (2 : ℕ))) * (y ^ (2 : ℕ)))) + (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) * (z ^ (2 : ℕ)))) - ((((2 * x_0) * y_0) * x) * y)) - ((((2 * y_0) * z_0) * y) * z)) - ((((2 * z_0) * x_0) * z) * x)) - ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ))))) ≤ 0 := by
  sorry

theorem proof_gap_exercise_3579_6
  (x_0 : ℝ)
  (y_0 : ℝ)
  (z_0 : ℝ)
  (R : ℝ)
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : y_0 ∈ (Set.univ : Set ℝ))
  (h3 : z_0 ∈ (Set.univ : Set ℝ))
  (h4 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h5 : S ⊆ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ))))
  (h6 : x ∈ (Set.univ : Set ℝ))
  (h7 : y ∈ (Set.univ : Set ℝ))
  (h8 : z ∈ (Set.univ : Set ℝ))
  (h9 : (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) + (z_0 ^ (2 : ℕ))) > (R ^ (2 : ℕ)))
  (h10 : l_0 = (x_0, y_0, z_0))
  (h11 : r = (x, y, z))
  (h12 : ((((x - x_0) ^ (2 : ℕ)) + ((y - y_0) ^ (2 : ℕ))) + ((z - z_0) ^ (2 : ℕ))) ≤ (R ^ (2 : ℕ)))
  (h13 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) = ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  (h14 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) ≤ ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  (h15 : (((((x * y_0) - (y * x_0)) ^ (2 : ℕ)) + (((y * z_0) - (z * y_0)) ^ (2 : ℕ))) + (((z * x_0) - (x * z_0)) ^ (2 : ℕ))) ≤ ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ)))))
  (h16 : (((((((((y_0 ^ (2 : ℕ)) + (z_0 ^ (2 : ℕ))) * (x ^ (2 : ℕ))) + (((x_0 ^ (2 : ℕ)) + (z_0 ^ (2 : ℕ))) * (y ^ (2 : ℕ)))) + (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) * (z ^ (2 : ℕ)))) - ((((2 * x_0) * y_0) * x) * y)) - ((((2 * y_0) * z_0) * y) * z)) - ((((2 * z_0) * x_0) * z) * x)) - ((R ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) + (z ^ (2 : ℕ))))) ≤ 0)
  : (S = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ ((((((((((y_0 ^ (2 : ℕ)) + (z_0 ^ (2 : ℕ))) * (p.1 ^ (2 : ℕ))) + (((x_0 ^ (2 : ℕ)) + (z_0 ^ (2 : ℕ))) * (p.2.1 ^ (2 : ℕ)))) + (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) * (p.2.2 ^ (2 : ℕ)))) - ((((2 * x_0) * y_0) * p.1) * p.2.1)) - ((((2 * y_0) * z_0) * p.2.1) * p.2.2)) - ((((2 * z_0) * x_0) * p.2.2) * p.1)) - ((R ^ (2 : ℕ)) * (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) + (p.2.2 ^ (2 : ℕ))))) ≤ 0)})) → (S = ({p : ℝ × (ℝ × ℝ) | (((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2.1 ∈ (Set.univ : Set ℝ))) ∧ (p.2.2 ∈ (Set.univ : Set ℝ))) ∧ ((((((((((y_0 ^ (2 : ℕ)) + (z_0 ^ (2 : ℕ))) * (p.1 ^ (2 : ℕ))) + (((x_0 ^ (2 : ℕ)) + (z_0 ^ (2 : ℕ))) * (p.2.1 ^ (2 : ℕ)))) + (((x_0 ^ (2 : ℕ)) + (y_0 ^ (2 : ℕ))) * (p.2.2 ^ (2 : ℕ)))) - ((((2 * x_0) * y_0) * p.1) * p.2.1)) - ((((2 * y_0) * z_0) * p.2.1) * p.2.2)) - ((((2 * z_0) * x_0) * p.2.2) * p.1)) - ((R ^ (2 : ℕ)) * (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) + (p.2.2 ^ (2 : ℕ))))) ≤ 0)})) := by
  sorry
