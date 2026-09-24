import Mathlib

-- exercise: exercise_805
-- Regenerated from proofgap by the current printer.
-- Lean generation failed for gaps: none
-- Last gap: 22; compilation status: passed
-- Classification concerns only the last gap compilation, not every gap below.

-- Exercise 805, gap 1
namespace regenerated_exercise_805_gap_1

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

theorem proof_gap_exercise_805_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))) := by
  sorry
end regenerated_exercise_805_gap_1

-- Exercise 805, gap 2
namespace regenerated_exercise_805_gap_2

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

theorem proof_gap_exercise_805_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))) := by
  sorry
end regenerated_exercise_805_gap_2

-- Exercise 805, gap 3
namespace regenerated_exercise_805_gap_3

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

theorem proof_gap_exercise_805_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))) := by
  sorry
end regenerated_exercise_805_gap_3

-- Exercise 805, gap 4
namespace regenerated_exercise_805_gap_4

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

theorem proof_gap_exercise_805_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))) := by
  sorry
end regenerated_exercise_805_gap_4

-- Exercise 805, gap 5
namespace regenerated_exercise_805_gap_5

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

theorem proof_gap_exercise_805_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))) := by
  sorry
end regenerated_exercise_805_gap_5

-- Exercise 805, gap 6
namespace regenerated_exercise_805_gap_6

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

theorem proof_gap_exercise_805_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))) := by
  sorry
end regenerated_exercise_805_gap_6

-- Exercise 805, gap 7
namespace regenerated_exercise_805_gap_7

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

theorem proof_gap_exercise_805_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))) := by
  sorry
end regenerated_exercise_805_gap_7

-- Exercise 805, gap 8
namespace regenerated_exercise_805_gap_8

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

theorem proof_gap_exercise_805_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))) := by
  sorry
end regenerated_exercise_805_gap_8

-- Exercise 805, gap 9
namespace regenerated_exercise_805_gap_9

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

theorem proof_gap_exercise_805_9
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))) := by
  sorry
end regenerated_exercise_805_gap_9

-- Exercise 805, gap 10
namespace regenerated_exercise_805_gap_10

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

theorem proof_gap_exercise_805_10
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))) := by
  sorry
end regenerated_exercise_805_gap_10

-- Exercise 805, gap 11
namespace regenerated_exercise_805_gap_11

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

theorem proof_gap_exercise_805_11
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))) := by
  sorry
end regenerated_exercise_805_gap_11

-- Exercise 805, gap 12
namespace regenerated_exercise_805_gap_12

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

theorem proof_gap_exercise_805_12
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))) := by
  sorry
end regenerated_exercise_805_gap_12

-- Exercise 805, gap 13
namespace regenerated_exercise_805_gap_13

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

theorem proof_gap_exercise_805_13
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))) := by
  sorry
end regenerated_exercise_805_gap_13

-- Exercise 805, gap 14
namespace regenerated_exercise_805_gap_14

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

theorem proof_gap_exercise_805_14
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))) := by
  sorry
end regenerated_exercise_805_gap_14

-- Exercise 805, gap 15
namespace regenerated_exercise_805_gap_15

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

theorem proof_gap_exercise_805_15
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  (h26 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))))
  : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Iio b))) := by
  sorry
end regenerated_exercise_805_gap_15

-- Exercise 805, gap 16
namespace regenerated_exercise_805_gap_16

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

theorem proof_gap_exercise_805_16
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  (h26 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))))
  (h27 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Iio b))))
  : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), (((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Ioi 0))) ∧ (x_2 ∈ (Set.Ioi 0))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_1)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))) := by
  sorry
end regenerated_exercise_805_gap_16

-- Exercise 805, gap 17
namespace regenerated_exercise_805_gap_17

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

theorem proof_gap_exercise_805_17
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  (h26 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))))
  (h27 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Iio b))))
  (h28 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), (((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Ioi 0))) ∧ (x_2 ∈ (Set.Ioi 0))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_1)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_2 : ℝ), (((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_2 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Iio 1))) ∧ (x_2 ∈ (Set.Iio 1))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_2)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))) := by
  sorry
end regenerated_exercise_805_gap_17

-- Exercise 805, gap 18
namespace regenerated_exercise_805_gap_18

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

theorem proof_gap_exercise_805_18
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  (h26 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))))
  (h27 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Iio b))))
  (h28 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), (((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Ioi 0))) ∧ (x_2 ∈ (Set.Ioi 0))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_1)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h29 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_2 : ℝ), (((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_2 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Iio 1))) ∧ (x_2 ∈ (Set.Iio 1))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_2)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h30 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), ((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (exists (v_uCE_uB4_2 : ℝ), ((((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (v_uCE_uB4_2 > 0)) ∧ (v_uCE_uB4 = (min (min (1 : ℝ) v_uCE_uB4_1) v_uCE_uB4_2))))))))))
  : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (((x_1 ∈ (Set.Ioi 0)) ∧ (x_2 ∈ (Set.Ioi 0))) ∨ ((x_1 ∈ (Set.Iio 1)) ∧ (x_2 ∈ (Set.Iio 1))))))))))) := by
  sorry
end regenerated_exercise_805_gap_18

-- Exercise 805, gap 19
namespace regenerated_exercise_805_gap_19

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

theorem proof_gap_exercise_805_19
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  (h26 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))))
  (h27 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Iio b))))
  (h28 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), (((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Ioi 0))) ∧ (x_2 ∈ (Set.Ioi 0))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_1)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h29 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_2 : ℝ), (((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_2 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Iio 1))) ∧ (x_2 ∈ (Set.Iio 1))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_2)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h30 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), ((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (exists (v_uCE_uB4_2 : ℝ), ((((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (v_uCE_uB4_2 > 0)) ∧ (v_uCE_uB4 = (min (min (1 : ℝ) v_uCE_uB4_1) v_uCE_uB4_2))))))))))
  (h31 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (((x_1 ∈ (Set.Ioi 0)) ∧ (x_2 ∈ (Set.Ioi 0))) ∨ ((x_1 ∈ (Set.Iio 1)) ∧ (x_2 ∈ (Set.Iio 1))))))))))))
  : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))) := by
  sorry
end regenerated_exercise_805_gap_19

-- Exercise 805, gap 20
namespace regenerated_exercise_805_gap_20

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

theorem proof_gap_exercise_805_20
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  (h26 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))))
  (h27 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Iio b))))
  (h28 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), (((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Ioi 0))) ∧ (x_2 ∈ (Set.Ioi 0))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_1)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h29 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_2 : ℝ), (((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_2 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Iio 1))) ∧ (x_2 ∈ (Set.Iio 1))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_2)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h30 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), ((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (exists (v_uCE_uB4_2 : ℝ), ((((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (v_uCE_uB4_2 > 0)) ∧ (v_uCE_uB4 = (min (min (1 : ℝ) v_uCE_uB4_1) v_uCE_uB4_2))))))))))
  (h31 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (((x_1 ∈ (Set.Ioi 0)) ∧ (x_2 ∈ (Set.Ioi 0))) ∨ ((x_1 ∈ (Set.Iio 1)) ∧ (x_2 ∈ (Set.Iio 1))))))))))))
  (h32 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f Set.univ)) := by
  sorry
end regenerated_exercise_805_gap_20

-- Exercise 805, gap 21
namespace regenerated_exercise_805_gap_21

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

theorem proof_gap_exercise_805_21
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  (h26 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))))
  (h27 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Iio b))))
  (h28 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), (((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Ioi 0))) ∧ (x_2 ∈ (Set.Ioi 0))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_1)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h29 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_2 : ℝ), (((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_2 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Iio 1))) ∧ (x_2 ∈ (Set.Iio 1))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_2)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h30 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), ((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (exists (v_uCE_uB4_2 : ℝ), ((((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (v_uCE_uB4_2 > 0)) ∧ (v_uCE_uB4 = (min (min (1 : ℝ) v_uCE_uB4_1) v_uCE_uB4_2))))))))))
  (h31 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (((x_1 ∈ (Set.Ioi 0)) ∧ (x_2 ∈ (Set.Ioi 0))) ∨ ((x_1 ∈ (Set.Iio 1)) ∧ (x_2 ∈ (Set.Iio 1))))))))))))
  (h32 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h33 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f Set.univ)))
  : UniformContinuousOn f (Set.Ioo a b) := by
  sorry
end regenerated_exercise_805_gap_21

-- Exercise 805, gap 22
namespace regenerated_exercise_805_gap_22

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

theorem proof_gap_exercise_805_22
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (v_uCE_uB4 : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : v_uCE_uB4 ∈ (Set.univ : Set ℝ))
  (h4 : ⊥ ≤ ((a : ℝ) : EReal))
  (h5 : a < b)
  (h6 : ((b : ℝ) : EReal) ≤ ⊤)
  (h7 : ContinuousOn f (Set.Ioo a b))
  (h8 : Bornology.IsBounded (f '' (Set.Ioo a b)))
  (h9 : (MonotoneOn f (Set.Ioo a b)) ∨ (AntitoneOn f (Set.Ioo a b)))
  (h10 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h11 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[<] b) (𝓝 B))))))
  (h12 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioo a b)) then (f x) else (if (x = a) then A else (if (x = b) then B else B)))))))
  (h13 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn f_star (Set.Icc a b))))
  (h14 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f_star (Set.Icc a b))))
  (h15 : (a ∈ (Set.univ : Set ℝ)) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Ioo a b))))
  (h16 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (A : ℝ), ((A ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] a) (𝓝 A))))))
  (h17 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (f_star = (fun (x : ℝ) => (if (x ∈ (Set.Ioi a)) then (f x) else (if (x = a) then A else A))))))
  (h18 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (ContinuousOn f_star (Set.Ici a))))
  (h19 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (exists (B : ℝ), ((B ∈ (Set.univ : Set ℝ)) ∧ (Tendsto (fun x : ℝ => (f_star x)) atTop (𝓝 B))))))
  (h20 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f_star (Set.Ici a))))
  (h21 : (a ∈ (Set.univ : Set ℝ)) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f (Set.Ioi a))))
  (h22 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (g = (fun (x : ℝ) => (f (-x))))))
  (h23 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (ContinuousOn g (Set.Ioi (-b)))))
  (h24 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (Bornology.IsBounded (g '' (Set.Ioi (-b))))))
  (h25 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → ((MonotoneOn g (Set.Ioi (-b))) ∨ (AntitoneOn g (Set.Ioi (-b))))))
  (h26 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn g (Set.Ioi (-b)))))
  (h27 : (((a : ℝ) : EReal) = ⊥) → ((b ∈ (Set.univ : Set ℝ)) → (UniformContinuousOn f (Set.Iio b))))
  (h28 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), (((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Ioi 0))) ∧ (x_2 ∈ (Set.Ioi 0))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_1)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h29 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_2 : ℝ), (((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_2 > 0)) ∧ (forall (x_1 : ℝ) (x_2 : ℝ), ((((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_2 ∈ (Set.univ : Set ℝ))) ∧ (x_1 ∈ (Set.Iio 1))) ∧ (x_2 ∈ (Set.Iio 1))) ∧ (|((x_1 - x_2))| < v_uCE_uB4_2)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h30 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (v_uCE_uB4_1 : ℝ), ((v_uCE_uB4_1 ∈ (Set.univ : Set ℝ)) ∧ (exists (v_uCE_uB4_2 : ℝ), ((((v_uCE_uB4_2 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4_1 > 0)) ∧ (v_uCE_uB4_2 > 0)) ∧ (v_uCE_uB4 = (min (min (1 : ℝ) v_uCE_uB4_1) v_uCE_uB4_2))))))))))
  (h31 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (((x_1 ∈ (Set.Ioi 0)) ∧ (x_2 ∈ (Set.Ioi 0))) ∨ ((x_1 ∈ (Set.Iio 1)) ∧ (x_2 ∈ (Set.Iio 1))))))))))))
  (h32 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → (forall (x_2 : ℝ), (((((x_2 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ Set.univ)) ∧ (x_2 ∈ Set.univ)) ∧ (|((x_1 - x_2))| < v_uCE_uB4)) → (|(((f x_1) - (f x_2)))| < v_uCE_uB5)))))))))
  (h33 : (((a : ℝ) : EReal) = ⊥) → ((((b : ℝ) : EReal) = ⊤) → (UniformContinuousOn f Set.univ)))
  (h34 : UniformContinuousOn f (Set.Ioo a b))
  : UniformContinuousOn f (Set.Ioo a b) := by
  sorry
end regenerated_exercise_805_gap_22

