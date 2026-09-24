import Mathlib

-- exercise: exercise_2172
-- Regenerated from proofgap by the current printer.
-- Lean generation failed for gaps: none
-- Last gap: 18; compilation status: passed
-- Classification concerns only the last gap compilation, not every gap below.

-- Exercise 2172, gap 1
namespace regenerated_exercise_2172_gap_1

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

theorem proof_gap_exercise_2172_1
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  : Continuous v_uCF_u86 := by
  sorry
end regenerated_exercise_2172_gap_1

-- Exercise 2172, gap 2
namespace regenerated_exercise_2172_gap_2

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

theorem proof_gap_exercise_2172_2
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  : ContDiff ℝ 1 F := by
  sorry
end regenerated_exercise_2172_gap_2

-- Exercise 2172, gap 3
namespace regenerated_exercise_2172_gap_3

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

theorem proof_gap_exercise_2172_3
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))) := by
  sorry
end regenerated_exercise_2172_gap_3

-- Exercise 2172, gap 4
namespace regenerated_exercise_2172_gap_4

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

theorem proof_gap_exercise_2172_4
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))) := by
  sorry
end regenerated_exercise_2172_gap_4

-- Exercise 2172, gap 5
namespace regenerated_exercise_2172_gap_5

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

theorem proof_gap_exercise_2172_5
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))) := by
  sorry
end regenerated_exercise_2172_gap_5

-- Exercise 2172, gap 6
namespace regenerated_exercise_2172_gap_6

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

theorem proof_gap_exercise_2172_6
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))) := by
  sorry
end regenerated_exercise_2172_gap_6

-- Exercise 2172, gap 7
namespace regenerated_exercise_2172_gap_7

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

theorem proof_gap_exercise_2172_7
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))) := by
  sorry
end regenerated_exercise_2172_gap_7

-- Exercise 2172, gap 8
namespace regenerated_exercise_2172_gap_8

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

theorem proof_gap_exercise_2172_8
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))) := by
  sorry
end regenerated_exercise_2172_gap_8

-- Exercise 2172, gap 9
namespace regenerated_exercise_2172_gap_9

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

theorem proof_gap_exercise_2172_9
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))) := by
  sorry
end regenerated_exercise_2172_gap_9

-- Exercise 2172, gap 10
namespace regenerated_exercise_2172_gap_10

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

theorem proof_gap_exercise_2172_10
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))) := by
  sorry
end regenerated_exercise_2172_gap_10

-- Exercise 2172, gap 11
namespace regenerated_exercise_2172_gap_11

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

theorem proof_gap_exercise_2172_11
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  (h14 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))))
  : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C (n_1 + 1)) = (((C n_1) + n_1) + (3 /. 4)))))) := by
  sorry
end regenerated_exercise_2172_gap_11

-- Exercise 2172, gap 12
namespace regenerated_exercise_2172_gap_12

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

theorem proof_gap_exercise_2172_12
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  (h14 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))))
  (h15 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C (n_1 + 1)) = (((C n_1) + n_1) + (3 /. 4)))))))
  : 0 = (F (0 : ℝ)) := by
  sorry
end regenerated_exercise_2172_gap_12

-- Exercise 2172, gap 13
namespace regenerated_exercise_2172_gap_13

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

theorem proof_gap_exercise_2172_13
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  (h14 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))))
  (h15 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C (n_1 + 1)) = (((C n_1) + n_1) + (3 /. 4)))))))
  (h16 : 0 = (F (0 : ℝ)))
  : (exists (C : (ℤ -> ℝ)), ((F (0 : ℝ)) = (C (0 : ℤ)))) := by
  sorry
end regenerated_exercise_2172_gap_13

-- Exercise 2172, gap 14
namespace regenerated_exercise_2172_gap_14

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

theorem proof_gap_exercise_2172_14
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  (h14 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))))
  (h15 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C (n_1 + 1)) = (((C n_1) + n_1) + (3 /. 4)))))))
  (h16 : 0 = (F (0 : ℝ)))
  (h17 : (exists (C : (ℤ -> ℝ)), ((F (0 : ℝ)) = (C (0 : ℤ)))))
  : (exists (C : (ℤ -> ℝ)), (0 = (C (0 : ℤ)))) := by
  sorry
end regenerated_exercise_2172_gap_14

-- Exercise 2172, gap 15
namespace regenerated_exercise_2172_gap_15

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

theorem proof_gap_exercise_2172_15
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  (h14 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))))
  (h15 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C (n_1 + 1)) = (((C n_1) + n_1) + (3 /. 4)))))))
  (h16 : 0 = (F (0 : ℝ)))
  (h17 : (exists (C : (ℤ -> ℝ)), ((F (0 : ℝ)) = (C (0 : ℤ)))))
  (h18 : (exists (C : (ℤ -> ℝ)), (0 = (C (0 : ℤ)))))
  : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C n_1) = (((1 /. 4) * n_1) * ((2 * n_1) + 1)))))) := by
  sorry
end regenerated_exercise_2172_gap_15

-- Exercise 2172, gap 16
namespace regenerated_exercise_2172_gap_16

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

theorem proof_gap_exercise_2172_16
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  (h14 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))))
  (h15 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C (n_1 + 1)) = (((C n_1) + n_1) + (3 /. 4)))))))
  (h16 : 0 = (F (0 : ℝ)))
  (h17 : (exists (C : (ℤ -> ℝ)), ((F (0 : ℝ)) = (C (0 : ℤ)))))
  (h18 : (exists (C : (ℤ -> ℝ)), (0 = (C (0 : ℤ)))))
  (h19 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C n_1) = (((1 /. 4) * n_1) * ((2 * n_1) + 1)))))))
  : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (((1 /. 4) * n_1) * ((2 * n_1) + 1)))))) := by
  sorry
end regenerated_exercise_2172_gap_16

-- Exercise 2172, gap 17
namespace regenerated_exercise_2172_gap_17

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

theorem proof_gap_exercise_2172_17
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  (h14 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))))
  (h15 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C (n_1 + 1)) = (((C n_1) + n_1) + (3 /. 4)))))))
  (h16 : 0 = (F (0 : ℝ)))
  (h17 : (exists (C : (ℤ -> ℝ)), ((F (0 : ℝ)) = (C (0 : ℤ)))))
  (h18 : (exists (C : (ℤ -> ℝ)), (0 = (C (0 : ℤ)))))
  (h19 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C n_1) = (((1 /. 4) * n_1) * ((2 * n_1) + 1)))))))
  (h20 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (((1 /. 4) * n_1) * ((2 * n_1) + 1)))))))
  : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - (((1 /. 4) * ((2 * n_1) + 1)) * (n_1 + 1)))))) := by
  sorry
end regenerated_exercise_2172_gap_17

-- Exercise 2172, gap 18
namespace regenerated_exercise_2172_gap_18

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

theorem proof_gap_exercise_2172_18
  (F : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (r : (ℝ -> ℝ))
  (n : ℤ)
  (h1 : n ∈ (Set.univ : Set ℤ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 x) = (sInf ({Abs_Minus_x_n | (n ∈ (Set.univ : Set ℤ))}))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((r x) = (x - ⌊x⌋)))))
  (h4 : (F (0 : ℝ)) = 0)
  (h5 : Continuous v_uCF_u86)
  (h6 : ContDiff ℝ 1 F)
  (h7 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((v_uCF_u86 x) = (x - n_1)))))
  (h8 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((v_uCF_u86 x) = (((-x) + n_1) + 1)))))
  (h9 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (C n_1)))))))
  (h10 : (exists (C' : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) + (C' n_1)))))))
  (h11 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + (1 /. 2))) (𝓝 (F (n_1 + (1 /. 2))))))))
  (h12 : (exists (C' : (ℤ -> ℝ)), (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C' n_1) = ((C n_1) - ((n_1 + (1 /. 2)) ^ (2 : ℕ)))))))))
  (h13 : (exists (C : (ℤ -> ℝ)), (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = ((((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - ((n_1 + (1 /. 2)) ^ (2 : ℕ))) + (C n_1)))))))
  (h14 : (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → (Tendsto (fun x : ℝ => (F x)) (𝓝[<] (n_1 + 1)) (𝓝 (F (n_1 + 1)))))))
  (h15 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C (n_1 + 1)) = (((C n_1) + n_1) + (3 /. 4)))))))
  (h16 : 0 = (F (0 : ℝ)))
  (h17 : (exists (C : (ℤ -> ℝ)), ((F (0 : ℝ)) = (C (0 : ℤ)))))
  (h18 : (exists (C : (ℤ -> ℝ)), (0 = (C (0 : ℤ)))))
  (h19 : (exists (C : (ℤ -> ℝ)), (forall (n_1 : ℤ), ((n_1 ∈ (Set.univ : Set ℤ)) → ((C n_1) = (((1 /. 4) * n_1) * ((2 * n_1) + 1)))))))
  (h20 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ (n_1 ≤ x)) ∧ (x < (n_1 + (1 /. 2)))) → ((F x) = ((((x ^ (2 : ℕ)) /. 2) - (n_1 * x)) + (((1 /. 4) * n_1) * ((2 * n_1) + 1)))))))
  (h21 : (forall (x : ℝ) (n_1 : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ (Set.univ : Set ℤ))) ∧ ((n_1 + (1 /. 2)) ≤ x)) ∧ (x < (n_1 + 1))) → ((F x) = (((-((x ^ (2 : ℕ)) /. 2)) + ((n_1 + 1) * x)) - (((1 /. 4) * ((2 * n_1) + 1)) * (n_1 + 1)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((F x) = ((x /. 4) + (((1 /. 4) * ((r x) - (1 /. 2))) * (1 - (2 * |(((r x) - (1 /. 2)))|))))))) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (((iteratedDeriv 1 (fun t => F t) x) = (v_uCF_u86 x)) ∧ ((F (0 : ℝ)) = 0)))) := by
  sorry
end regenerated_exercise_2172_gap_18

