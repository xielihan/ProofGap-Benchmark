import Mathlib

-- exercise: exercise_407_1
-- Regenerated from proofgap by the current printer.
-- Lean generation failed for gaps: none
-- Last gap: 3; compilation status: passed
-- Classification concerns only the last gap compilation, not every gap below.

-- Exercise 407_1, gap 1
namespace regenerated_exercise_407_1_gap_1

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

theorem proof_gap_exercise_407_1_1
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (D : (Set ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : y = f)
  (h5 : (a ∈ { cluster : ℝ | AccPt cluster (𝓟 D) }))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] a) (𝓝 b))
  (h7 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (x ≠ a)) → ((y x) < b))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (0 < |((x - a))|)) ∧ (|((x - a))| < v_uCE_uB4)) → ((0 < (b - (y x))) ∧ ((b - (y x)) < v_uCE_uB5)))))))) := by
  sorry
end regenerated_exercise_407_1_gap_1

-- Exercise 407_1, gap 2
namespace regenerated_exercise_407_1_gap_2

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

theorem proof_gap_exercise_407_1_2
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (D : (Set ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : y = f)
  (h5 : (a ∈ { cluster : ℝ | AccPt cluster (𝓟 D) }))
  (h6 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (0 < |((x - a))|)) ∧ (|((x - a))| < v_uCE_uB4)) → ((0 < (b - (y x))) ∧ ((b - (y x)) < v_uCE_uB5)))))))))
  : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] a) (𝓝 (b - 0)) := by
  sorry
end regenerated_exercise_407_1_gap_2

-- Exercise 407_1, gap 3
namespace regenerated_exercise_407_1_gap_3

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

theorem proof_gap_exercise_407_1_3
  (y : (ℝ -> ℝ))
  (f : (ℝ -> ℝ))
  (D : (Set ℝ))
  (a : ℝ)
  (b : ℝ)
  (h1 : D ⊆ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : y = f)
  (h5 : (a ∈ { cluster : ℝ | AccPt cluster (𝓟 D) }))
  (h6 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ D)) ∧ (0 < |((x - a))|)) ∧ (|((x - a))| < v_uCE_uB4)) → ((0 < (b - (y x))) ∧ ((b - (y x)) < v_uCE_uB5)))))))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[≠] a) (𝓝 (b - 0)))
  : Tendsto (fun x : ℝ => (fun (x_1 : ℝ) => (-|(x_1)|))) (𝓝[≠] 0) (𝓝 (0 - 0)) := by
  sorry
end regenerated_exercise_407_1_gap_3

