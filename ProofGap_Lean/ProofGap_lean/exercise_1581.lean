import Mathlib

-- exercise: exercise_1581
-- Regenerated from proofgap by the current printer.
-- Lean generation failed for gaps: none
-- Last gap: 10; compilation status: passed
-- Classification concerns only the last gap compilation, not every gap below.

-- Exercise 1581, gap 1
namespace regenerated_exercise_1581_gap_1

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_1
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) := by
  sorry
end regenerated_exercise_1581_gap_1

-- Exercise 1581, gap 2
namespace regenerated_exercise_1581_gap_2

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_2
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) := by
  sorry
end regenerated_exercise_1581_gap_2

-- Exercise 1581, gap 3
namespace regenerated_exercise_1581_gap_3

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_3
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h13 : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  : (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi))) = (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi))) := by
  sorry
end regenerated_exercise_1581_gap_3

-- Exercise 1581, gap 4
namespace regenerated_exercise_1581_gap_4

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_4
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h13 : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h14 : (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi))) = (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi))))
  : (iteratedDeriv 1 (fun t => f t) x) = (((16 * (Real.pi ^ (2 : ℕ))) * (x ^ (3 : ℕ))) - (6 * (x ^ (5 : ℕ)))) := by
  sorry
end regenerated_exercise_1581_gap_4

-- Exercise 1581, gap 5
namespace regenerated_exercise_1581_gap_5

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_5
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h13 : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h14 : (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi))) = (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi))))
  (h15 : (iteratedDeriv 1 (fun t => f t) x) = (((16 * (Real.pi ^ (2 : ℕ))) * (x ^ (3 : ℕ))) - (6 * (x ^ (5 : ℕ)))))
  : ((iteratedDeriv 1 (fun t => f t) x) = 0) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))) := by
  sorry
end regenerated_exercise_1581_gap_5

-- Exercise 1581, gap 6
namespace regenerated_exercise_1581_gap_6

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_6
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h13 : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h14 : (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi))) = (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi))))
  (h15 : (iteratedDeriv 1 (fun t => f t) x) = (((16 * (Real.pi ^ (2 : ℕ))) * (x ^ (3 : ℕ))) - (6 * (x ^ (5 : ℕ)))))
  (h16 : ((iteratedDeriv 1 (fun t => f t) x) = 0) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))))
  : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → ((iteratedDeriv 1 (fun t => f t) x) = 0) := by
  sorry
end regenerated_exercise_1581_gap_6

-- Exercise 1581, gap 7
namespace regenerated_exercise_1581_gap_7

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_7
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h13 : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h14 : (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi))) = (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi))))
  (h15 : (iteratedDeriv 1 (fun t => f t) x) = (((16 * (Real.pi ^ (2 : ℕ))) * (x ^ (3 : ℕ))) - (6 * (x ^ (5 : ℕ)))))
  (h16 : ((iteratedDeriv 1 (fun t => f t) x) = 0) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))))
  (h17 : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → ((iteratedDeriv 1 (fun t => f t) x) = 0))
  : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))) := by
  sorry
end regenerated_exercise_1581_gap_7

-- Exercise 1581, gap 8
namespace regenerated_exercise_1581_gap_8

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_8
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h13 : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h14 : (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi))) = (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi))))
  (h15 : (iteratedDeriv 1 (fun t => f t) x) = (((16 * (Real.pi ^ (2 : ℕ))) * (x ^ (3 : ℕ))) - (6 * (x ^ (5 : ℕ)))))
  (h16 : ((iteratedDeriv 1 (fun t => f t) x) = 0) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))))
  (h17 : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → ((iteratedDeriv 1 (fun t => f t) x) = 0))
  (h18 : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))))
  : (V ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) = (sSup (V '' (Set.Ioo 0 (2 * Real.pi)))) := by
  sorry
end regenerated_exercise_1581_gap_8

-- Exercise 1581, gap 9
namespace regenerated_exercise_1581_gap_9

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_9
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h13 : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h14 : (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi))) = (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi))))
  (h15 : (iteratedDeriv 1 (fun t => f t) x) = (((16 * (Real.pi ^ (2 : ℕ))) * (x ^ (3 : ℕ))) - (6 * (x ^ (5 : ℕ)))))
  (h16 : ((iteratedDeriv 1 (fun t => f t) x) = 0) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))))
  (h17 : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → ((iteratedDeriv 1 (fun t => f t) x) = 0))
  (h18 : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))))
  (h19 : (V ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) = (sSup (V '' (Set.Ioo 0 (2 * Real.pi)))))
  : v_uCE_uB8 = ((2 * Real.pi) * (1 - (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) := by
  sorry
end regenerated_exercise_1581_gap_9

-- Exercise 1581, gap 10
namespace regenerated_exercise_1581_gap_10

attribute [local instance] Classical.propDecidable

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

theorem proof_gap_exercise_1581_10
  (V : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (x : ℝ)
  (h : ℝ)
  (v_uCE_uB8 : ℝ)
  (h1 : R ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : h ∈ (Set.univ : Set ℝ))
  (h4 : v_uCE_uB8 ∈ (Set.univ : Set ℝ))
  (h5 : R > 0)
  (h6 : 0 < x)
  (h7 : x < (2 * Real.pi))
  (h8 : h = (Real.rpow ((R ^ (2 : ℕ)) - (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) (((2 : ℝ))⁻¹)))
  (h9 : (V x) = ((((1 /. 3) * Real.pi) * (((R * x) /. (2 * Real.pi)) ^ (2 : ℕ))) * h))
  (h10 : (f x) = ((x ^ (4 : ℕ)) * ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ)))))
  (h11 : v_uCE_uB8 = ((2 * Real.pi) - x))
  (h12 : h = ((R /. (2 * Real.pi)) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h13 : (V x) = ((((R ^ (3 : ℕ)) /. (24 * (Real.pi ^ (2 : ℕ)))) * (x ^ (2 : ℕ))) * (Real.rpow ((4 * (Real.pi ^ (2 : ℕ))) - (x ^ (2 : ℕ))) (((2 : ℝ))⁻¹))))
  (h14 : (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi))) = (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi))))
  (h15 : (iteratedDeriv 1 (fun t => f t) x) = (((16 * (Real.pi ^ (2 : ℕ))) * (x ^ (3 : ℕ))) - (6 * (x ^ (5 : ℕ)))))
  (h16 : ((iteratedDeriv 1 (fun t => f t) x) = 0) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))))
  (h17 : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → ((iteratedDeriv 1 (fun t => f t) x) = 0))
  (h18 : (x = ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) → (x ∈ (lpMaximumPointsOn f (Set.Ioo 0 (2 * Real.pi)))))
  (h19 : (V ((2 * Real.pi) * (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))) = (sSup (V '' (Set.Ioo 0 (2 * Real.pi)))))
  (h20 : v_uCE_uB8 = ((2 * Real.pi) * (1 - (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹)))))
  : (v_uCE_uB8 = ((2 * Real.pi) * (1 - (Real.rpow (2 /. 3) (((2 : ℝ))⁻¹))))) → (x ∈ (lpMaximumPointsOn V (Set.Ioo 0 (2 * Real.pi)))) := by
  sorry
end regenerated_exercise_1581_gap_10

