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

-- exercise: exercise_3855

theorem proof_gap_exercise_3855_1
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : m > 0)
  (h4 : n ≠ 0)
  (h5 : t = (Real.rpow x m))
  : ((0 ≤ x) ∧ (x ≤ 1)) → ((0 ≤ t) ∧ (t ≤ 1)) := by
  sorry

theorem proof_gap_exercise_3855_2
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : m > 0)
  (h4 : n ≠ 0)
  (h5 : t = (Real.rpow x m))
  (h6 : ((0 ≤ x) ∧ (x ≤ 1)) → ((0 ≤ t) ∧ (t ≤ 1)))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3855_3
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : m > 0)
  (h4 : n ≠ 0)
  (h5 : t = (Real.rpow x m))
  (h6 : ((0 ≤ x) ∧ (x ≤ 1)) → ((0 ≤ t) ∧ (t ≤ 1)))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  : ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))) := by
  sorry

theorem proof_gap_exercise_3855_4
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : m > 0)
  (h4 : n ≠ 0)
  (h5 : t = (Real.rpow x m))
  (h6 : ((0 ≤ x) ∧ (x ≤ 1)) → ((0 ≤ t) ∧ (t ≤ 1)))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  (h8 : ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))) := by
  sorry

theorem proof_gap_exercise_3855_5
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : m > 0)
  (h4 : n ≠ 0)
  (h5 : t = (Real.rpow x m))
  (h6 : ((0 ≤ x) ∧ (x ≤ 1)) → ((0 ≤ t) ∧ (t ≤ 1)))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  (h8 : ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))))
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))))
  : ((1 - (1 /. n)) > 0) ↔ ((n < 0) ∨ (n > 1)) := by
  sorry

theorem proof_gap_exercise_3855_6
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : m > 0)
  (h4 : n ≠ 0)
  (h5 : t = (Real.rpow x m))
  (h6 : ((0 ≤ x) ∧ (x ≤ 1)) → ((0 ≤ t) ∧ (t ≤ 1)))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  (h8 : ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))))
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))))
  (h10 : ((1 - (1 /. n)) > 0) ↔ ((n < 0) ∨ (n > 1)))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))) := by
  sorry

theorem proof_gap_exercise_3855_7
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : m > 0)
  (h4 : n ≠ 0)
  (h5 : t = (Real.rpow x m))
  (h6 : ((0 ≤ x) ∧ (x ≤ 1)) → ((0 ≤ t) ∧ (t ≤ 1)))
  (h7 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))))
  (h8 : ((1 /. m) * (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t ((1 /. m) - 1)) * (Real.rpow (1 - t) (-(1 /. n)))) * (1 : ℝ)))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))))
  (h9 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))))
  (h10 : ((1 - (1 /. n)) > 0) ↔ ((n < 0) ∨ (n > 1)))
  (h11 : (∫ x in (0 : ℝ)..(1 : ℝ), (((1 : ℝ) /. (Real.rpow (1 - (Real.rpow x m)) ((n)⁻¹))) * (1 : ℝ))) = ((1 /. m) * (B ((1 /. m), (1 - (1 /. n))))))
  : (n < 0) ∨ (n > 1) := by
  sorry
