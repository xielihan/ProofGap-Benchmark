import Mathlib

-- exercise: exercise_3801
-- Regenerated from proofgap by the current printer.
-- Lean generation failed for gaps: gap 18, gap 19, gap 20, gap 21, gap 22, gap 23, gap 24, gap 25, gap 26, gap 27, gap 28, gap 29
-- Last gap: 29; compilation status: last_gap_not_printed
-- Classification concerns only the last gap compilation, not every gap below.

-- Exercise 3801, gap 1
namespace regenerated_exercise_3801_gap_1

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

theorem proof_gap_exercise_3801_1
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))) := by
  sorry
end regenerated_exercise_3801_gap_1

-- Exercise 3801, gap 2
namespace regenerated_exercise_3801_gap_2

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

theorem proof_gap_exercise_3801_2
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))) := by
  sorry
end regenerated_exercise_3801_gap_2

-- Exercise 3801, gap 3
namespace regenerated_exercise_3801_gap_3

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

theorem proof_gap_exercise_3801_3
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))) := by
  sorry
end regenerated_exercise_3801_gap_3

-- Exercise 3801, gap 4
namespace regenerated_exercise_3801_gap_4

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

theorem proof_gap_exercise_3801_4
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))) := by
  sorry
end regenerated_exercise_3801_gap_4

-- Exercise 3801, gap 5
namespace regenerated_exercise_3801_gap_5

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

theorem proof_gap_exercise_3801_5
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))) := by
  sorry
end regenerated_exercise_3801_gap_5

-- Exercise 3801, gap 6
namespace regenerated_exercise_3801_gap_6

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

theorem proof_gap_exercise_3801_6
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))) := by
  sorry
end regenerated_exercise_3801_gap_6

-- Exercise 3801, gap 7
namespace regenerated_exercise_3801_gap_7

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

theorem proof_gap_exercise_3801_7
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))) := by
  sorry
end regenerated_exercise_3801_gap_7

-- Exercise 3801, gap 8
namespace regenerated_exercise_3801_gap_8

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

theorem proof_gap_exercise_3801_8
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))) := by
  sorry
end regenerated_exercise_3801_gap_8

-- Exercise 3801, gap 9
namespace regenerated_exercise_3801_gap_9

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

theorem proof_gap_exercise_3801_9
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))) := by
  sorry
end regenerated_exercise_3801_gap_9

-- Exercise 3801, gap 10
namespace regenerated_exercise_3801_gap_10

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

theorem proof_gap_exercise_3801_10
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  (h11 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → ((1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) ≤ (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))) := by
  sorry
end regenerated_exercise_3801_gap_10

-- Exercise 3801, gap 11
namespace regenerated_exercise_3801_gap_11

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

theorem proof_gap_exercise_3801_11
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  (h11 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))))
  (h12 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → ((1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) ≤ (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))) := by
  sorry
end regenerated_exercise_3801_gap_11

-- Exercise 3801, gap 12
namespace regenerated_exercise_3801_gap_12

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

theorem proof_gap_exercise_3801_12
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  (h11 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))))
  (h12 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → ((1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) ≤ (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h13 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (MeasureTheory.IntegrableOn (fun x : ℝ => (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))) (Set.Ioi (0 : ℝ)) MeasureTheory.volume))))) := by
  sorry
end regenerated_exercise_3801_gap_12

-- Exercise 3801, gap 13
namespace regenerated_exercise_3801_gap_13

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

theorem proof_gap_exercise_3801_13
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  (h11 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))))
  (h12 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → ((1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) ≤ (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h13 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h14 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (MeasureTheory.IntegrableOn (fun x : ℝ => (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))) (Set.Ioi (0 : ℝ)) MeasureTheory.volume))))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn K ((Set.Ioi 0) ×ˢ (Set.Ioi 0))))) := by
  sorry
end regenerated_exercise_3801_gap_13

-- Exercise 3801, gap 14
namespace regenerated_exercise_3801_gap_14

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

theorem proof_gap_exercise_3801_14
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  (h11 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))))
  (h12 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → ((1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) ≤ (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h13 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h14 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (MeasureTheory.IntegrableOn (fun x : ℝ => (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))) (Set.Ioi (0 : ℝ)) MeasureTheory.volume))))))
  (h15 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn K ((Set.Ioi 0) ×ˢ (Set.Ioi 0))))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((K (v_uCE_uB1, v_uCE_uB2)) = ((((v_uCE_uB1 ^ (2 : ℕ)) /. ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))) * (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ)))) - (((v_uCE_uB2 ^ (2 : ℕ)) /. ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))) * (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))))))))) := by
  sorry
end regenerated_exercise_3801_gap_14

-- Exercise 3801, gap 15
namespace regenerated_exercise_3801_gap_15

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

theorem proof_gap_exercise_3801_15
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  (h11 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))))
  (h12 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → ((1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) ≤ (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h13 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h14 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (MeasureTheory.IntegrableOn (fun x : ℝ => (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))) (Set.Ioi (0 : ℝ)) MeasureTheory.volume))))))
  (h15 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn K ((Set.Ioi 0) ×ˢ (Set.Ioi 0))))))
  (h16 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((K (v_uCE_uB1, v_uCE_uB2)) = ((((v_uCE_uB1 ^ (2 : ℕ)) /. ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))) * (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ)))) - (((v_uCE_uB2 ^ (2 : ℕ)) /. ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))) * (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))))))))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((K (v_uCE_uB1, v_uCE_uB2)) = (((v_uCE_uB1 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ))))) - ((v_uCE_uB2 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))))))))) := by
  sorry
end regenerated_exercise_3801_gap_15

-- Exercise 3801, gap 16
namespace regenerated_exercise_3801_gap_16

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

theorem proof_gap_exercise_3801_16
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  (h11 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))))
  (h12 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → ((1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) ≤ (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h13 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h14 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (MeasureTheory.IntegrableOn (fun x : ℝ => (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))) (Set.Ioi (0 : ℝ)) MeasureTheory.volume))))))
  (h15 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn K ((Set.Ioi 0) ×ˢ (Set.Ioi 0))))))
  (h16 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((K (v_uCE_uB1, v_uCE_uB2)) = ((((v_uCE_uB1 ^ (2 : ℕ)) /. ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))) * (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ)))) - (((v_uCE_uB2 ^ (2 : ℕ)) /. ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))) * (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))))))))))
  (h17 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((K (v_uCE_uB1, v_uCE_uB2)) = (((v_uCE_uB1 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ))))) - ((v_uCE_uB2 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))))))))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((((v_uCE_uB1 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ))))) - ((v_uCE_uB2 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))))) = (Real.pi /. (2 * (v_uCE_uB1 + v_uCE_uB2))))))) := by
  sorry
end regenerated_exercise_3801_gap_16

-- Exercise 3801, gap 17
namespace regenerated_exercise_3801_gap_17

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

theorem proof_gap_exercise_3801_17
  (I : (ℝ × ℝ -> ℝ))
  (J : (ℝ × ℝ -> ℝ))
  (K : (ℝ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (v_uCE_uB2 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB2 ∈ (Set.univ : Set ℝ))
  (h3 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (Tendsto (fun x : ℝ => (((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (v_uCE_uB1 * v_uCE_uB2)))))
  (h4 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))))| < (((Real.pi ^ (2 : ℕ)) /. 4) * (1 /. (x ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 ^ (2 : ℕ))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))
  (h6 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((I (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), ((((Real.arctan (v_uCE_uB1 * x)) * (Real.arctan (v_uCE_uB2 * x))) /. (x ^ (2 : ℕ))) * (1 : ℝ)))) → (ContinuousOn I ((Set.Ici 0) ×ˢ (Set.Ici 0))))))
  (h7 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (|(((Real.arctan (v_uCE_uB2 * x)) /. (x * (1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))| < ((Real.pi /. 2) * (1 /. (x * (1 + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))))
  (h8 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x_1)) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB1_0 : ℝ), (((((((v_uCE_uB1_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_0 > 0)) ∧ (v_uCE_uB1 ≥ v_uCE_uB1_0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ (1 ≤ x)) ∧ (((x : ℝ) : EReal) < ⊤)) → (MeasureTheory.IntegrableOn (fun x_1 : ℝ => (((1 : ℝ) /. (x_1 * ((1 : ℝ) + ((v_uCE_uB1_0 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))) (Set.Ioi (1 : ℝ)) MeasureTheory.volume))))))
  (h9 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn J ((Set.Ioi 0) ×ˢ (Set.Ici 0))))))
  (h10 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((J (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((Real.arctan (v_uCE_uB2 * x)) /. (x * ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB1_1 : ℝ), ((v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB2_1 : ℝ), ((((v_uCE_uB2_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 > 0)) ∧ (v_uCE_uB2_1 ≥ 0)) → ((iteratedDeriv 1 (fun t => I (t, v_uCE_uB2_1)) v_uCE_uB1_1) = (J (v_uCE_uB1_1, v_uCE_uB2_1))))))))))
  (h11 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))))))))))
  (h12 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → ((1 /. ((1 + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * (1 + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) ≤ (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h13 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1 ≥ 0)) ∧ (v_uCE_uB2 ≥ 0)) ∧ ((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x_1 in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x_1 ^ (2 : ℕ)))))) * (1 : ℝ))))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (0 < (1 /. (1 + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))))))))
  (h14 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (forall (v_uCE_uB2_0 : ℝ), (((((v_uCE_uB2_0 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB2_0 > 0)) ∧ (v_uCE_uB2 ≥ v_uCE_uB2_0)) ∧ (v_uCE_uB1 > 0)) → (MeasureTheory.IntegrableOn (fun x : ℝ => (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2_0 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))) (Set.Ioi (0 : ℝ)) MeasureTheory.volume))))))
  (h15 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → (ContinuousOn K ((Set.Ioi 0) ×ˢ (Set.Ioi 0))))))
  (h16 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((K (v_uCE_uB1, v_uCE_uB2)) = ((((v_uCE_uB1 ^ (2 : ℕ)) /. ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))) * (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ)))) - (((v_uCE_uB2 ^ (2 : ℕ)) /. ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))) * (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ))))) * (1 : ℝ))))))))))
  (h17 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((K (v_uCE_uB1, v_uCE_uB2)) = (((v_uCE_uB1 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ))))) - ((v_uCE_uB2 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))))))))))
  (h18 : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((((v_uCE_uB1 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ))))) - ((v_uCE_uB2 * Real.pi) /. (2 * ((v_uCE_uB1 ^ (2 : ℕ)) - (v_uCE_uB2 ^ (2 : ℕ)))))) = (Real.pi /. (2 * (v_uCE_uB1 + v_uCE_uB2))))))))
  : (v_uCE_uB1 ≥ 0) → ((v_uCE_uB2 ≥ 0) → (((K (v_uCE_uB1, v_uCE_uB2)) = (∫ x in Set.Ioi (0 : ℝ), (((1 : ℝ) /. (((1 : ℝ) + ((v_uCE_uB1 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))) * ((1 : ℝ) + ((v_uCE_uB2 ^ (2 : ℕ)) * (x ^ (2 : ℕ)))))) * (1 : ℝ)))) → ((v_uCE_uB1 ≠ v_uCE_uB2) → ((K (v_uCE_uB1, v_uCE_uB2)) = (Real.pi /. (2 * (v_uCE_uB1 + v_uCE_uB2))))))) := by
  sorry
end regenerated_exercise_3801_gap_17

