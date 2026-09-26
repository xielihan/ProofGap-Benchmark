import Mathlib

-- exercise: exercise_436
-- Regenerated for Lean 4.29.0-rc6 / Mathlib 5c8398d.

-- Source: proofgap/exercise_436/1.txt
namespace regenerated_exercise_436_gap_1

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

theorem proof_gap_exercise_436_1
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((1 + (Real.rpow x (-(1 /. 6)))) + (Real.rpow x (-(1 /. 4)))) /. (Real.rpow (2 + (1 /. x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((Real.rpow x (((2 : ℝ))⁻¹)) + (Real.rpow x (((3 : ℝ))⁻¹))) + (Real.rpow x (((4 : ℝ))⁻¹))) /. (Real.rpow ((2 * x) + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 (limUnder atTop (fun x : ℝ => (((1 + (Real.rpow x (-(1 /. 6)))) + (Real.rpow x (-(1 /. 4)))) /. (Real.rpow (2 + (1 /. x)) (((2 : ℝ))⁻¹)))))))) := by
  sorry

end regenerated_exercise_436_gap_1

-- Source: proofgap/exercise_436/2.txt
namespace regenerated_exercise_436_gap_2

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

theorem proof_gap_exercise_436_2
  (h1 : Tendsto (fun x : ℝ => ((((Real.rpow x (((2 : ℝ))⁻¹)) + (Real.rpow x (((3 : ℝ))⁻¹))) + (Real.rpow x (((4 : ℝ))⁻¹))) /. (Real.rpow ((2 * x) + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 (limUnder atTop (fun x : ℝ => (((1 + (Real.rpow x (-(1 /. 6)))) + (Real.rpow x (-(1 /. 4)))) /. (Real.rpow (2 + (1 /. x)) (((2 : ℝ))⁻¹)))))))
  (h2 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 + (Real.rpow x (-(1 /. 6)))) + (Real.rpow x (-(1 /. 4)))) /. (Real.rpow (2 + (1 /. x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => (((1 + (Real.rpow x (-(1 /. 6)))) + (Real.rpow x (-(1 /. 4)))) /. (Real.rpow (2 + (1 /. x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

end regenerated_exercise_436_gap_2

-- Source: proofgap/exercise_436/3.txt
namespace regenerated_exercise_436_gap_3

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

theorem proof_gap_exercise_436_3
  (h1 : Tendsto (fun x : ℝ => ((((Real.rpow x (((2 : ℝ))⁻¹)) + (Real.rpow x (((3 : ℝ))⁻¹))) + (Real.rpow x (((4 : ℝ))⁻¹))) /. (Real.rpow ((2 * x) + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 (limUnder atTop (fun x : ℝ => (((1 + (Real.rpow x (-(1 /. 6)))) + (Real.rpow x (-(1 /. 4)))) /. (Real.rpow (2 + (1 /. x)) (((2 : ℝ))⁻¹)))))))
  (h2 : Tendsto (fun x : ℝ => (((1 + (Real.rpow x (-(1 /. 6)))) + (Real.rpow x (-(1 /. 4)))) /. (Real.rpow (2 + (1 /. x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 + (Real.rpow x (-(1 /. 6)))) + (Real.rpow x (-(1 /. 4)))) /. (Real.rpow (2 + (1 /. x)) (((2 : ℝ))⁻¹)))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => ((((Real.rpow x (((2 : ℝ))⁻¹)) + (Real.rpow x (((3 : ℝ))⁻¹))) + (Real.rpow x (((4 : ℝ))⁻¹))) /. (Real.rpow ((2 * x) + 1) (((2 : ℝ))⁻¹)))) atTop (𝓝 (1 /. (Real.rpow (2 : ℝ) (((2 : ℝ))⁻¹)))) := by
  sorry

end regenerated_exercise_436_gap_3
