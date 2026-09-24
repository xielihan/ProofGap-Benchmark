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

-- exercise: exercise_2514

theorem proof_gap_exercise_2514_1
  (a : ℝ)
  (p : ℝ)
  (C : (ℝ × ℝ))
  (x : ℝ)
  (y : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h3 : C ∈ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h4 : R ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h8 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h9 : R = ({p_1 : ℝ × ℝ | (p_1.1 ∈ (Set.univ : Set ℝ)) ∧ (p_1.2 ∈ (Set.univ : Set ℝ)) ∧ ((0 ≤ p_1.1) ∧ (p_1.1 ≤ a)) ∧ ((p_1.2 ^ (2 : ℕ)) ≤ ((2 * p) * p_1.1))}))
  (h10 : v_uCE_uBE = ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))))
  : v_uCE_uB7 = 0 := by
  sorry

theorem proof_gap_exercise_2514_2
  (a : ℝ)
  (p : ℝ)
  (C : (ℝ × ℝ))
  (x : ℝ)
  (y : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h3 : C ∈ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h4 : R ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h8 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h9 : R = ({p_1 : ℝ × ℝ | (p_1.1 ∈ (Set.univ : Set ℝ)) ∧ (p_1.2 ∈ (Set.univ : Set ℝ)) ∧ ((0 ≤ p_1.1) ∧ (p_1.1 ≤ a)) ∧ ((p_1.2 ^ (2 : ℕ)) ≤ ((2 * p) * p_1.1))}))
  (h10 : v_uCE_uB7 = 0)
  (h11 : ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))) = ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))))
  : v_uCE_uBE = ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2514_3
  (a : ℝ)
  (p : ℝ)
  (C : (ℝ × ℝ))
  (x : ℝ)
  (y : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h3 : C ∈ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h4 : R ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h8 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h9 : R = ({p_1 : ℝ × ℝ | (p_1.1 ∈ (Set.univ : Set ℝ)) ∧ (p_1.2 ∈ (Set.univ : Set ℝ)) ∧ ((0 ≤ p_1.1) ∧ (p_1.1 ≤ a)) ∧ ((p_1.2 ^ (2 : ℕ)) ≤ ((2 * p) * p_1.1))}))
  (h10 : v_uCE_uB7 = 0)
  (h11 : v_uCE_uBE = ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))))
  (h12 : ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))) = ((2 /. 3) * a))
  : ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))) = ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2514_4
  (a : ℝ)
  (p : ℝ)
  (C : (ℝ × ℝ))
  (x : ℝ)
  (y : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h3 : C ∈ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h4 : R ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h8 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h9 : R = ({p_1 : ℝ × ℝ | (p_1.1 ∈ (Set.univ : Set ℝ)) ∧ (p_1.2 ∈ (Set.univ : Set ℝ)) ∧ ((0 ≤ p_1.1) ∧ (p_1.1 ≤ a)) ∧ ((p_1.2 ^ (2 : ℕ)) ≤ ((2 * p) * p_1.1))}))
  (h10 : v_uCE_uB7 = 0)
  (h11 : v_uCE_uBE = ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))))
  (h12 : ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))) = ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))))
  (h13 : v_uCE_uBE = ((2 /. 3) * a))
  : ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))) = ((2 /. 3) * a) := by
  sorry

theorem proof_gap_exercise_2514_5
  (a : ℝ)
  (p : ℝ)
  (C : (ℝ × ℝ))
  (x : ℝ)
  (y : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h3 : C ∈ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h4 : R ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h8 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h9 : R = ({p_1 : ℝ × ℝ | (p_1.1 ∈ (Set.univ : Set ℝ)) ∧ (p_1.2 ∈ (Set.univ : Set ℝ)) ∧ ((0 ≤ p_1.1) ∧ (p_1.1 ≤ a)) ∧ ((p_1.2 ^ (2 : ℕ)) ≤ ((2 * p) * p_1.1))}))
  (h10 : v_uCE_uB7 = 0)
  (h11 : v_uCE_uBE = ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))))
  (h12 : ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))) = ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))))
  (h13 : ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))) = ((2 /. 3) * a))
  : v_uCE_uBE = ((2 /. 3) * a) := by
  sorry

theorem proof_gap_exercise_2514_6
  (a : ℝ)
  (p : ℝ)
  (C : (ℝ × ℝ))
  (x : ℝ)
  (y : ℝ)
  (v_uCE_uBE : ℝ)
  (v_uCE_uB7 : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (p ∈ (Set.univ : Set ℝ)) ∧ (p > 0))
  (h3 : C ∈ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h4 : R ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h5 : x ∈ (Set.univ : Set ℝ))
  (h6 : y ∈ (Set.univ : Set ℝ))
  (h7 : v_uCE_uBE ∈ (Set.univ : Set ℝ))
  (h8 : v_uCE_uB7 ∈ (Set.univ : Set ℝ))
  (h9 : R = ({p_1 : ℝ × ℝ | (p_1.1 ∈ (Set.univ : Set ℝ)) ∧ (p_1.2 ∈ (Set.univ : Set ℝ)) ∧ ((0 ≤ p_1.1) ∧ (p_1.1 ≤ a)) ∧ ((p_1.2 ^ (2 : ℕ)) ≤ ((2 * p) * p_1.1))}))
  (h10 : v_uCE_uB7 = 0)
  (h11 : v_uCE_uBE = ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))))
  (h12 : ((∫ x_1 in (0 : ℝ)..a, (((x_1 * Real.pi) * (y ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((Real.pi * (y ^ (2 : ℕ))) * (1 : ℝ)))) = ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))))
  (h13 : ((∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * (x_1 ^ (2 : ℕ))) * (1 : ℝ))) /. (∫ x_1 in (0 : ℝ)..a, ((((2 : ℝ) * p) * x_1) * (1 : ℝ)))) = ((2 /. 3) * a))
  (h14 : v_uCE_uBE = ((2 /. 3) * a))
  : (C = (((2 /. 3) * a), 0)) → (C = (((2 /. 3) * a), 0)) := by
  sorry
