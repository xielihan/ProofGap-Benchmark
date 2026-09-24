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

-- exercise: exercise_3113

theorem proof_gap_exercise_3113_1
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_3113_2
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))) := by
  sorry

theorem proof_gap_exercise_3113_3
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))) := by
  sorry

theorem proof_gap_exercise_3113_4
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  (h6 : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))))
  : 0 < v_uCE_uB8_1 := by
  sorry

theorem proof_gap_exercise_3113_5
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  (h6 : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))))
  (h7 : 0 < v_uCE_uB8_1)
  : v_uCE_uB8_1 < 1 := by
  sorry

theorem proof_gap_exercise_3113_6
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  (h6 : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))))
  (h7 : 0 < v_uCE_uB8_1)
  (h8 : v_uCE_uB8_1 < 1)
  : 0 < v_uCE_uB8_2 := by
  sorry

theorem proof_gap_exercise_3113_7
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  (h6 : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))))
  (h7 : 0 < v_uCE_uB8_1)
  (h8 : v_uCE_uB8_1 < 1)
  (h9 : 0 < v_uCE_uB8_2)
  : v_uCE_uB8_2 < 1 := by
  sorry

theorem proof_gap_exercise_3113_8
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  (h6 : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))))
  (h7 : 0 < v_uCE_uB8_1)
  (h8 : v_uCE_uB8_1 < 1)
  (h9 : 0 < v_uCE_uB8_2)
  (h10 : v_uCE_uB8_2 < 1)
  : (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))) = (((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))) /. (((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 1000)))) := by
  sorry

theorem proof_gap_exercise_3113_9
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  (h6 : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))))
  (h7 : 0 < v_uCE_uB8_1)
  (h8 : v_uCE_uB8_1 < 1)
  (h9 : 0 < v_uCE_uB8_2)
  (h10 : v_uCE_uB8_2 < 1)
  (h11 : (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))) = (((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))) /. (((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 1000)))))
  : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = ((((00798 : ℝ) /. (10000 : ℝ))) * (Real.exp (v_uCE_uB8 /. 300))) := by
  sorry

theorem proof_gap_exercise_3113_10
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  (h6 : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))))
  (h7 : 0 < v_uCE_uB8_1)
  (h8 : v_uCE_uB8_1 < 1)
  (h9 : 0 < v_uCE_uB8_2)
  (h10 : v_uCE_uB8_2 < 1)
  (h11 : (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))) = (((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))) /. (((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 1000)))))
  (h12 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = ((((00798 : ℝ) /. (10000 : ℝ))) * (Real.exp (v_uCE_uB8 /. 300))))
  : |(v_uCE_uB8)| < 1 := by
  sorry

theorem proof_gap_exercise_3113_11
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8_1 : ℝ)
  (v_uCE_uB8_2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8_1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8_2 ∈ (Set.univ : Set ℝ))
  (h4 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))))
  (h5 : ((100 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))))
  (h6 : ((50 : ℕ))! = ((((Real.rpow ((2 * Real.pi) * 50) (((2 : ℝ))⁻¹)) * ((50 : ℕ) ^ (50 : ℕ))) * (Real.exp (-(50 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 2000))))
  (h7 : 0 < v_uCE_uB8_1)
  (h8 : v_uCE_uB8_1 < 1)
  (h9 : 0 < v_uCE_uB8_2)
  (h10 : v_uCE_uB8_2 < 1)
  (h11 : (((100 : ℕ))! /. (((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ)))) = (((((Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹)) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_1 /. 1020))) /. (((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8_2 /. 1000)))))
  (h12 : ((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) = ((((00798 : ℝ) /. (10000 : ℝ))) * (Real.exp (v_uCE_uB8 /. 300))))
  (h13 : |(v_uCE_uB8)| < 1)
  : |(((∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), ((2 * k) - 1)) /. (∏ k ∈ Finset.Icc (1 : ℕ) (50 : ℕ), (2 * k))) - ((((00798 : ℝ) /. (10000 : ℝ))) * (1 + (v_uCE_uB8 /. 300))))| ≤ ((((00798 : ℝ) /. (10000 : ℝ))) /. 300) := by
  sorry
