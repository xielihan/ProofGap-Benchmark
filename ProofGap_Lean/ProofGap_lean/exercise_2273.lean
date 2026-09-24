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

-- exercise: exercise_2273

theorem proof_gap_exercise_2273_1
  (x : ℝ)
  (h1 : (1 + (3 * (x ^ (8 : ℕ)))) = t)
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1)))
  : t ∈ (Set.Icc 1 4) := by
  sorry

theorem proof_gap_exercise_2273_2
  (h1 : (1 + (3 * (x ^ (8 : ℕ)))) = t)
  (h2 : t ∈ (Set.Icc 1 4))
  : ((24 * (x ^ (7 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = (fderiv ℝ (fun (t : ℝ) => t)) := by
  sorry

theorem proof_gap_exercise_2273_3
  (h1 : (1 + (3 * (x ^ (8 : ℕ)))) = t)
  (h2 : t ∈ (Set.Icc 1 4))
  (h3 : ((24 * (x ^ (7 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = (fderiv ℝ (fun (t : ℝ) => t)))
  : (x ^ (8 : ℕ)) = ((1 /. 3) * (t - 1)) := by
  sorry

theorem proof_gap_exercise_2273_4
  (h1 : (1 + (3 * (x ^ (8 : ℕ)))) = t)
  (h2 : t ∈ (Set.Icc 1 4))
  (h3 : ((24 * (x ^ (7 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = (fderiv ℝ (fun (t : ℝ) => t)))
  (h4 : (x ^ (8 : ℕ)) = ((1 /. 3) * (t - 1)))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (15 : ℕ)) * (Real.rpow (1 + (3 * (x ^ (8 : ℕ)))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((1 /. 72) * (∫ t in (1 : ℝ)..(4 : ℝ), (((t - (1 : ℝ)) * (Real.rpow t (1 /. 2))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2273_5
  (h1 : (1 + (3 * (x ^ (8 : ℕ)))) = t)
  (h2 : t ∈ (Set.Icc 1 4))
  (h3 : ((24 * (x ^ (7 : ℕ))) • (fderiv ℝ (fun (x : ℝ) => x))) = (fderiv ℝ (fun (t : ℝ) => t)))
  (h4 : (x ^ (8 : ℕ)) = ((1 /. 3) * (t - 1)))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (15 : ℕ)) * (Real.rpow (1 + (3 * (x ^ (8 : ℕ)))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = ((1 /. 72) * (∫ t in (1 : ℝ)..(4 : ℝ), (((t - (1 : ℝ)) * (Real.rpow t (1 /. 2))) * (1 : ℝ)))))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (((x ^ (15 : ℕ)) * (Real.rpow (1 + (3 * (x ^ (8 : ℕ)))) (((2 : ℝ))⁻¹))) * (1 : ℝ))) = (29 /. 270) := by
  sorry
