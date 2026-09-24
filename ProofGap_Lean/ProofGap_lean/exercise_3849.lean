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

-- exercise: exercise_3849

theorem proof_gap_exercise_3849_1
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  : 0 ≤ x := by
  sorry

theorem proof_gap_exercise_3849_2
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  (h4 : 0 ≤ x)
  : x ≤ 1 := by
  sorry

theorem proof_gap_exercise_3849_3
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  : 0 ≤ t := by
  sorry

theorem proof_gap_exercise_3849_4
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : 0 ≤ t)
  : t ≤ 1 := by
  sorry

theorem proof_gap_exercise_3849_5
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : 0 ≤ t)
  (h7 : t ≤ 1)
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ n)) (((n : ℝ))⁻¹))) * (1 : ℝ))) = ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3849_6
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : 0 ≤ t)
  (h7 : t ≤ 1)
  (h8 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ n)) (((n : ℝ))⁻¹))) * (1 : ℝ))) = ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  : ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. n) * (B ((1 /. n), ((n - 1) /. n)))) := by
  sorry

theorem proof_gap_exercise_3849_7
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : 0 ≤ t)
  (h7 : t ≤ 1)
  (h8 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ n)) (((n : ℝ))⁻¹))) * (1 : ℝ))) = ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  (h9 : ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. n) * (B ((1 /. n), ((n - 1) /. n)))))
  : ((1 /. n) * (B ((1 /. n), ((n - 1) /. n)))) = ((1 /. n) * (((v_uCE_u93 (1 /. n)) * (v_uCE_u93 ((n - 1) /. n))) /. (v_uCE_u93 (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3849_8
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : 0 ≤ t)
  (h7 : t ≤ 1)
  (h8 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ n)) (((n : ℝ))⁻¹))) * (1 : ℝ))) = ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  (h9 : ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. n) * (B ((1 /. n), ((n - 1) /. n)))))
  (h10 : ((1 /. n) * (B ((1 /. n), ((n - 1) /. n)))) = ((1 /. n) * (((v_uCE_u93 (1 /. n)) * (v_uCE_u93 ((n - 1) /. n))) /. (v_uCE_u93 (1 : ℝ)))))
  : ((1 /. n) * (((v_uCE_u93 (1 /. n)) * (v_uCE_u93 ((n - 1) /. n))) /. (v_uCE_u93 (1 : ℝ)))) = (Real.pi /. (n * (Real.sin (Real.pi /. n)))) := by
  sorry

theorem proof_gap_exercise_3849_9
  (B : (ℝ × ℝ -> ℝ))
  (v_uCE_u93 : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n > 1)
  (h3 : t = (x ^ n))
  (h4 : 0 ≤ x)
  (h5 : x ≤ 1)
  (h6 : 0 ≤ t)
  (h7 : t ≤ 1)
  (h8 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ n)) (((n : ℝ))⁻¹))) * (1 : ℝ))) = ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  (h9 : ((1 /. n) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 - n) /. n)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. n) * (B ((1 /. n), ((n - 1) /. n)))))
  (h10 : ((1 /. n) * (B ((1 /. n), ((n - 1) /. n)))) = ((1 /. n) * (((v_uCE_u93 (1 /. n)) * (v_uCE_u93 ((n - 1) /. n))) /. (v_uCE_u93 (1 : ℝ)))))
  (h11 : ((1 /. n) * (((v_uCE_u93 (1 /. n)) * (v_uCE_u93 ((n - 1) /. n))) /. (v_uCE_u93 (1 : ℝ)))) = (Real.pi /. (n * (Real.sin (Real.pi /. n)))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (x ^ n)) (((n : ℝ))⁻¹))) * (1 : ℝ))) = (Real.pi /. (n * (Real.sin (Real.pi /. n)))) := by
  sorry
