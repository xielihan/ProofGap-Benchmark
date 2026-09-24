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

-- exercise: exercise_3116

theorem proof_gap_exercise_3116_1
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8__1 : ℝ)
  (v_uCE_uB8__2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8__1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8__2 ∈ (Set.univ : Set ℝ))
  (h4 : |(v_uCE_uB8)| < 1)
  (h5 : 0 < v_uCE_uB8__1)
  (h6 : v_uCE_uB8__1 < 1)
  (h7 : 0 < v_uCE_uB8__2)
  (h8 : v_uCE_uB8__2 < 1)
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3116_2
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8__1 : ℝ)
  (v_uCE_uB8__2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8__1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8__2 ∈ (Set.univ : Set ℝ))
  (h4 : |(v_uCE_uB8)| < 1)
  (h5 : 0 < v_uCE_uB8__1)
  (h6 : v_uCE_uB8__1 < 1)
  (h7 : 0 < v_uCE_uB8__2)
  (h8 : v_uCE_uB8__2 < 1)
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))))
  : (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))) = ((((100 : ℕ))!)! /. (((101 : ℕ))!)!) := by
  sorry

theorem proof_gap_exercise_3116_3
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8__1 : ℝ)
  (v_uCE_uB8__2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8__1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8__2 ∈ (Set.univ : Set ℝ))
  (h4 : |(v_uCE_uB8)| < 1)
  (h5 : 0 < v_uCE_uB8__1)
  (h6 : v_uCE_uB8__1 < 1)
  (h7 : 0 < v_uCE_uB8__2)
  (h8 : v_uCE_uB8__2 < 1)
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))) = ((((100 : ℕ))!)! /. (((101 : ℕ))!)!))
  : ((((100 : ℕ))!)! /. (((101 : ℕ))!)!) = ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!) := by
  sorry

theorem proof_gap_exercise_3116_4
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8__1 : ℝ)
  (v_uCE_uB8__2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8__1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8__2 ∈ (Set.univ : Set ℝ))
  (h4 : |(v_uCE_uB8)| < 1)
  (h5 : 0 < v_uCE_uB8__1)
  (h6 : v_uCE_uB8__1 < 1)
  (h7 : 0 < v_uCE_uB8__2)
  (h8 : v_uCE_uB8__2 < 1)
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))) = ((((100 : ℕ))!)! /. (((101 : ℕ))!)!))
  (h11 : ((((100 : ℕ))!)! /. (((101 : ℕ))!)!) = ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!))
  : ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!) = ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))) := by
  sorry

theorem proof_gap_exercise_3116_5
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8__1 : ℝ)
  (v_uCE_uB8__2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8__1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8__2 ∈ (Set.univ : Set ℝ))
  (h4 : |(v_uCE_uB8)| < 1)
  (h5 : 0 < v_uCE_uB8__1)
  (h6 : v_uCE_uB8__1 < 1)
  (h7 : 0 < v_uCE_uB8__2)
  (h8 : v_uCE_uB8__2 < 1)
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))) = ((((100 : ℕ))!)! /. (((101 : ℕ))!)!))
  (h11 : ((((100 : ℕ))!)! /. (((101 : ℕ))!)!) = ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!))
  (h12 : ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!) = ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))))
  : ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))) = (((10 * (Real.rpow Real.pi (((2 : ℝ))⁻¹))) /. (101 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.exp (v_uCE_uB8 /. 300))) := by
  sorry

theorem proof_gap_exercise_3116_6
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8__1 : ℝ)
  (v_uCE_uB8__2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8__1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8__2 ∈ (Set.univ : Set ℝ))
  (h4 : |(v_uCE_uB8)| < 1)
  (h5 : 0 < v_uCE_uB8__1)
  (h6 : v_uCE_uB8__1 < 1)
  (h7 : 0 < v_uCE_uB8__2)
  (h8 : v_uCE_uB8__2 < 1)
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))) = ((((100 : ℕ))!)! /. (((101 : ℕ))!)!))
  (h11 : ((((100 : ℕ))!)! /. (((101 : ℕ))!)!) = ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!))
  (h12 : ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!) = ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))))
  (h13 : ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))) = (((10 * (Real.rpow Real.pi (((2 : ℝ))⁻¹))) /. (101 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.exp (v_uCE_uB8 /. 300))))
  : (((10 * (Real.rpow Real.pi (((2 : ℝ))⁻¹))) /. (101 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.exp (v_uCE_uB8 /. 300))) = ((((01241 : ℝ) /. (10000 : ℝ))) * (Real.exp (v_uCE_uB8 /. 300))) := by
  sorry

theorem proof_gap_exercise_3116_7
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8__1 : ℝ)
  (v_uCE_uB8__2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8__1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8__2 ∈ (Set.univ : Set ℝ))
  (h4 : |(v_uCE_uB8)| < 1)
  (h5 : 0 < v_uCE_uB8__1)
  (h6 : v_uCE_uB8__1 < 1)
  (h7 : 0 < v_uCE_uB8__2)
  (h8 : v_uCE_uB8__2 < 1)
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))) = ((((100 : ℕ))!)! /. (((101 : ℕ))!)!))
  (h11 : ((((100 : ℕ))!)! /. (((101 : ℕ))!)!) = ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!))
  (h12 : ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!) = ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))))
  (h13 : ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))) = (((10 * (Real.rpow Real.pi (((2 : ℝ))⁻¹))) /. (101 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.exp (v_uCE_uB8 /. 300))))
  (h14 : (((10 * (Real.rpow Real.pi (((2 : ℝ))⁻¹))) /. (101 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.exp (v_uCE_uB8 /. 300))) = ((((01241 : ℝ) /. (10000 : ℝ))) * (Real.exp (v_uCE_uB8 /. 300))))
  : |(((((01241 : ℝ) /. (10000 : ℝ))) * (Real.exp (v_uCE_uB8 /. 300))) - ((((01241 : ℝ) /. (10000 : ℝ))) * (1 + (v_uCE_uB8 /. 300))))| ≤ (1 /. 300) := by
  sorry

theorem proof_gap_exercise_3116_8
  (v_uCE_uB8 : ℝ)
  (v_uCE_uB8__1 : ℝ)
  (v_uCE_uB8__2 : ℝ)
  (h1 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB8__1 ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB8__2 ∈ (Set.univ : Set ℝ))
  (h4 : |(v_uCE_uB8)| < 1)
  (h5 : 0 < v_uCE_uB8__1)
  (h6 : v_uCE_uB8__1 < 1)
  (h7 : 0 < v_uCE_uB8__2)
  (h8 : v_uCE_uB8__2 < 1)
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(Real.pi /. 2), (((Real.cos t) ^ (101 : ℕ)) * (1 : ℝ))) = ((((100 : ℕ))!)! /. (((101 : ℕ))!)!))
  (h11 : ((((100 : ℕ))!)! /. (((101 : ℕ))!)!) = ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!))
  (h12 : ((((2 : ℕ) ^ (100 : ℕ)) * (((50 : ℕ))! ^ (2 : ℕ))) /. ((101 : ℕ))!) = ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))))
  (h13 : ((((((((2 : ℕ) ^ (100 : ℕ)) * 100) * Real.pi) * ((50 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__1 /. 300))) /. ((((101 * (Real.rpow ((2 * Real.pi) * 100) (((2 : ℝ))⁻¹))) * ((100 : ℕ) ^ (100 : ℕ))) * (Real.exp (-(100 : ℝ)))) * (Real.exp (v_uCE_uB8__2 /. 1200)))) = (((10 * (Real.rpow Real.pi (((2 : ℝ))⁻¹))) /. (101 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.exp (v_uCE_uB8 /. 300))))
  (h14 : (((10 * (Real.rpow Real.pi (((2 : ℝ))⁻¹))) /. (101 * (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) * (Real.exp (v_uCE_uB8 /. 300))) = ((((01241 : ℝ) /. (10000 : ℝ))) * (Real.exp (v_uCE_uB8 /. 300))))
  (h15 : |(((((01241 : ℝ) /. (10000 : ℝ))) * (Real.exp (v_uCE_uB8 /. 300))) - ((((01241 : ℝ) /. (10000 : ℝ))) * (1 + (v_uCE_uB8 /. 300))))| ≤ (1 /. 300))
  : |((∫ x in (0 : ℝ)..(1 : ℝ), (((1 - (x ^ (2 : ℕ))) ^ (50 : ℕ)) * (1 : ℝ))) - ((((01241 : ℝ) /. (10000 : ℝ))) * (1 + (v_uCE_uB8 /. 300))))| ≤ (1 /. 300) := by
  sorry
