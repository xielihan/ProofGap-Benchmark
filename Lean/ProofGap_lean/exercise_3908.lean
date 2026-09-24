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

-- exercise: exercise_3908

theorem proof_gap_exercise_3908_1
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  : (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), ((∫ r in (0 : ℝ)..a, (((r ^ (2 : ℕ)) * ((Real.sin v_uCF_u86) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) = (((a ^ (3 : ℕ)) /. 3) * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (((Real.sin v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3908_2
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), ((∫ r in (0 : ℝ)..a, (((r ^ (2 : ℕ)) * ((Real.sin v_uCF_u86) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) = (((a ^ (3 : ℕ)) /. 3) * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (((Real.sin v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))))
  : (((a ^ (3 : ℕ)) /. 3) * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (((Real.sin v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))) = (((a ^ (3 : ℕ)) /. 3) * ((((2 * Real.pi) /. 2) - ((1 /. 4) * (Real.sin (2 * (2 * Real.pi))))) - ((0 /. 2) - ((1 /. 4) * (Real.sin (2 * 0)))))) := by
  sorry

theorem proof_gap_exercise_3908_3
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), ((∫ r in (0 : ℝ)..a, (((r ^ (2 : ℕ)) * ((Real.sin v_uCF_u86) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) = (((a ^ (3 : ℕ)) /. 3) * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (((Real.sin v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))))
  (h4 : (((a ^ (3 : ℕ)) /. 3) * (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), (((Real.sin v_uCF_u86) ^ (2 : ℕ)) * (1 : ℝ)))) = (((a ^ (3 : ℕ)) /. 3) * ((((2 * Real.pi) /. 2) - ((1 /. 4) * (Real.sin (2 * (2 * Real.pi))))) - ((0 /. 2) - ((1 /. 4) * (Real.sin (2 * 0)))))))
  : (∫ v_uCF_u86 in (0 : ℝ)..(2 * Real.pi), ((∫ r in (0 : ℝ)..a, (((r ^ (2 : ℕ)) * ((Real.sin v_uCF_u86) ^ (2 : ℕ))) * (1 : ℝ))) * (1 : ℝ))) = ((Real.pi * (a ^ (3 : ℕ))) /. 3) := by
  sorry
