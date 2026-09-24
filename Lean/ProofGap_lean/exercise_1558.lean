import Mathlib

-- exercise: exercise_1558
-- Regenerated from proofgap by the current printer.
-- Lean generation failed for gaps: none
-- Last gap: 8; compilation status: passed
-- Classification concerns only the last gap compilation, not every gap below.

-- Exercise 1558, gap 1
namespace regenerated_exercise_1558_gap_1

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

theorem proof_gap_exercise_1558_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((f x) = ((Real.rpow x m) * (Real.rpow (a - x) n))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.rpow x (m - 1)) * (Real.rpow (a - x) (n - 1))) * ((m * a) - ((m + n) * x)))))) := by
  sorry
end regenerated_exercise_1558_gap_1

-- Exercise 1558, gap 2
namespace regenerated_exercise_1558_gap_2

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

theorem proof_gap_exercise_1558_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((f x) = ((Real.rpow x m) * (Real.rpow (a - x) n))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.rpow x (m - 1)) * (Real.rpow (a - x) (n - 1))) * ((m * a) - ((m + n) * x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => f t) x) = 0)) → (x = ((m * a) /. (m + n))))) := by
  sorry
end regenerated_exercise_1558_gap_2

-- Exercise 1558, gap 3
namespace regenerated_exercise_1558_gap_3

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

theorem proof_gap_exercise_1558_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((f x) = ((Real.rpow x m) * (Real.rpow (a - x) n))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.rpow x (m - 1)) * (Real.rpow (a - x) (n - 1))) * ((m * a) - ((m + n) * x)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => f t) x) = 0)) → (x = ((m * a) /. (m + n))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < ((m * a) /. (m + n)))) → ((iteratedDeriv 1 (fun t => f t) x) > 0))) := by
  sorry
end regenerated_exercise_1558_gap_3

-- Exercise 1558, gap 4
namespace regenerated_exercise_1558_gap_4

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

theorem proof_gap_exercise_1558_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((f x) = ((Real.rpow x m) * (Real.rpow (a - x) n))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.rpow x (m - 1)) * (Real.rpow (a - x) (n - 1))) * ((m * a) - ((m + n) * x)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => f t) x) = 0)) → (x = ((m * a) /. (m + n))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < ((m * a) /. (m + n)))) → ((iteratedDeriv 1 (fun t => f t) x) > 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((m * a) /. (m + n)) < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) < 0))) := by
  sorry
end regenerated_exercise_1558_gap_4

-- Exercise 1558, gap 5
namespace regenerated_exercise_1558_gap_5

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

theorem proof_gap_exercise_1558_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((f x) = ((Real.rpow x m) * (Real.rpow (a - x) n))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.rpow x (m - 1)) * (Real.rpow (a - x) (n - 1))) * ((m * a) - ((m + n) * x)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => f t) x) = 0)) → (x = ((m * a) /. (m + n))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < ((m * a) /. (m + n)))) → ((iteratedDeriv 1 (fun t => f t) x) > 0))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((m * a) /. (m + n)) < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) < 0))))
  : (lpMaximumPointsOn f (Set.Ioo 0 a)) = ({x | x = ((m * a) /. (m + n))}) := by
  sorry
end regenerated_exercise_1558_gap_5

-- Exercise 1558, gap 6
namespace regenerated_exercise_1558_gap_6

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

theorem proof_gap_exercise_1558_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((f x) = ((Real.rpow x m) * (Real.rpow (a - x) n))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.rpow x (m - 1)) * (Real.rpow (a - x) (n - 1))) * ((m * a) - ((m + n) * x)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => f t) x) = 0)) → (x = ((m * a) /. (m + n))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < ((m * a) /. (m + n)))) → ((iteratedDeriv 1 (fun t => f t) x) > 0))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((m * a) /. (m + n)) < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) < 0))))
  (h9 : (lpMaximumPointsOn f (Set.Ioo 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  : (sSup (f '' (Set.Ioo 0 a))) = (f ((m * a) /. (m + n))) := by
  sorry
end regenerated_exercise_1558_gap_6

-- Exercise 1558, gap 7
namespace regenerated_exercise_1558_gap_7

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

theorem proof_gap_exercise_1558_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((f x) = ((Real.rpow x m) * (Real.rpow (a - x) n))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.rpow x (m - 1)) * (Real.rpow (a - x) (n - 1))) * ((m * a) - ((m + n) * x)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => f t) x) = 0)) → (x = ((m * a) /. (m + n))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < ((m * a) /. (m + n)))) → ((iteratedDeriv 1 (fun t => f t) x) > 0))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((m * a) /. (m + n)) < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) < 0))))
  (h9 : (lpMaximumPointsOn f (Set.Ioo 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  (h10 : (sSup (f '' (Set.Ioo 0 a))) = (f ((m * a) /. (m + n))))
  : (f ((m * a) /. (m + n))) = ((((Real.rpow a (m + n)) * (Real.rpow m m)) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) := by
  sorry
end regenerated_exercise_1558_gap_7

-- Exercise 1558, gap 8
namespace regenerated_exercise_1558_gap_8

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

theorem proof_gap_exercise_1558_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (m : ℝ)
  (n : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (m ∈ (Set.univ : Set ℝ)) ∧ (m > 0))
  (h3 : (n ∈ (Set.univ : Set ℝ)) ∧ (n > 0))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((f x) = ((Real.rpow x m) * (Real.rpow (a - x) n))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.rpow x (m - 1)) * (Real.rpow (a - x) (n - 1))) * ((m * a) - ((m + n) * x)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t => f t) x) = 0)) → (x = ((m * a) /. (m + n))))))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < ((m * a) /. (m + n)))) → ((iteratedDeriv 1 (fun t => f t) x) > 0))))
  (h8 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((m * a) /. (m + n)) < x)) ∧ (x < a)) → ((iteratedDeriv 1 (fun t => f t) x) < 0))))
  (h9 : (lpMaximumPointsOn f (Set.Ioo 0 a)) = ({x | x = ((m * a) /. (m + n))}))
  (h10 : (sSup (f '' (Set.Ioo 0 a))) = (f ((m * a) /. (m + n))))
  (h11 : (f ((m * a) /. (m + n))) = ((((Real.rpow a (m + n)) * (Real.rpow m m)) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))))
  : (sSup (f '' (Set.Ioo 0 a))) = ((((Real.rpow a (m + n)) * (Real.rpow m m)) * (Real.rpow n n)) /. (Real.rpow (m + n) (m + n))) := by
  sorry
end regenerated_exercise_1558_gap_8

