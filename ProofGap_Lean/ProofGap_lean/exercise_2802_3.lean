import Mathlib

-- exercise: exercise_2802_3
-- Regenerated for Lean 4.29.0-rc6 / Mathlib 5c8398d.

-- Source: proofgap/exercise_2802_3/1.txt
namespace regenerated_exercise_2802_3_gap_1

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

theorem proof_gap_exercise_2802_3_1
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L) ∧ ((∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))) := by
  sorry

end regenerated_exercise_2802_3_gap_1

-- Source: proofgap/exercise_2802_3/2.txt
namespace regenerated_exercise_2802_3_gap_2

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

theorem proof_gap_exercise_2802_3_2
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0 := by
  sorry

end regenerated_exercise_2802_3_gap_2

-- Source: proofgap/exercise_2802_3/3.txt
namespace regenerated_exercise_2802_3_gap_3

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

theorem proof_gap_exercise_2802_3_3
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0 := by
  sorry

end regenerated_exercise_2802_3_gap_3

-- Source: proofgap/exercise_2802_3/4.txt
namespace regenerated_exercise_2802_3_gap_4

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

theorem proof_gap_exercise_2802_3_4
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0)
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ))) = ((Real.rpow (n : ℝ) v_uCE_uB1) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))))))) := by
  sorry

end regenerated_exercise_2802_3_gap_4

-- Source: proofgap/exercise_2802_3/5.txt
namespace regenerated_exercise_2802_3_gap_5

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

theorem proof_gap_exercise_2802_3_5
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0)
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ))) = ((Real.rpow (n : ℝ) v_uCE_uB1) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))))))))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))) = ((((-(1 /. n)) * (Real.exp (-(n : ℝ)))) - ((1 /. (n ^ (2 : ℕ))) * (Real.exp (-(n : ℝ))))) + (1 /. (n ^ (2 : ℕ))))))) := by
  sorry

end regenerated_exercise_2802_3_gap_5

-- Source: proofgap/exercise_2802_3/6.txt
namespace regenerated_exercise_2802_3_gap_6

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

theorem proof_gap_exercise_2802_3_6
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0)
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ))) = ((Real.rpow (n : ℝ) v_uCE_uB1) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))) = ((((-(1 /. n)) * (Real.exp (-(n : ℝ)))) - ((1 /. (n ^ (2 : ℕ))) * (Real.exp (-(n : ℝ))))) + (1 /. (n ^ (2 : ℕ))))))))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (limUnder atTop (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))))))) := by
  sorry

end regenerated_exercise_2802_3_gap_6

-- Source: proofgap/exercise_2802_3/7.txt
namespace regenerated_exercise_2802_3_gap_7

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

theorem proof_gap_exercise_2802_3_7
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0)
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ))) = ((Real.rpow (n : ℝ) v_uCE_uB1) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))) = ((((-(1 /. n)) * (Real.exp (-(n : ℝ)))) - ((1 /. (n ^ (2 : ℕ))) * (Real.exp (-(n : ℝ))))) + (1 /. (n ^ (2 : ℕ))))))))
  (h9 : Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (limUnder atTop (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))))))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 L))
  : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 0)) := by
  sorry

end regenerated_exercise_2802_3_gap_7

-- Source: proofgap/exercise_2802_3/8.txt
namespace regenerated_exercise_2802_3_gap_8

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

theorem proof_gap_exercise_2802_3_8
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0)
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ))) = ((Real.rpow (n : ℝ) v_uCE_uB1) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))) = ((((-(1 /. n)) * (Real.exp (-(n : ℝ)))) - ((1 /. (n ^ (2 : ℕ))) * (Real.exp (-(n : ℝ))))) + (1 /. (n ^ (2 : ℕ))))))))
  (h9 : Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (limUnder atTop (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))))))
  (h10 : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 0)))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  (h12 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 L))
  : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))))) := by
  sorry

end regenerated_exercise_2802_3_gap_8

-- Source: proofgap/exercise_2802_3/9.txt
namespace regenerated_exercise_2802_3_gap_9

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

theorem proof_gap_exercise_2802_3_9
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0)
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ))) = ((Real.rpow (n : ℝ) v_uCE_uB1) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))) = ((((-(1 /. n)) * (Real.exp (-(n : ℝ)))) - ((1 /. (n ^ (2 : ℕ))) * (Real.exp (-(n : ℝ))))) + (1 /. (n ^ (2 : ℕ))))))))
  (h9 : Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (limUnder atTop (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))))))
  (h10 : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 0)))
  (h11 : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))))))
  (h12 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  (h13 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 L))
  : (v_uCE_uB1 ≥ 2) → (Not (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 0))) := by
  sorry

end regenerated_exercise_2802_3_gap_9

-- Source: proofgap/exercise_2802_3/10.txt
namespace regenerated_exercise_2802_3_gap_10

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

theorem proof_gap_exercise_2802_3_10
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0)
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ))) = ((Real.rpow (n : ℝ) v_uCE_uB1) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))) = ((((-(1 /. n)) * (Real.exp (-(n : ℝ)))) - ((1 /. (n ^ (2 : ℕ))) * (Real.exp (-(n : ℝ))))) + (1 /. (n ^ (2 : ℕ))))))))
  (h9 : Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (limUnder atTop (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))))))
  (h10 : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 0)))
  (h11 : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))))))
  (h12 : (v_uCE_uB1 ≥ 2) → (Not (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 0))))
  (h13 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  (h14 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 L))
  : (v_uCE_uB1 ≥ 2) → (Not (Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ)))))) := by
  sorry

end regenerated_exercise_2802_3_gap_10

-- Source: proofgap/exercise_2802_3/11.txt
namespace regenerated_exercise_2802_3_gap_11

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

theorem proof_gap_exercise_2802_3_11
  (f : (ℕ × ℝ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → ((f (n, x)) = (((Real.rpow (n : ℝ) v_uCE_uB1) * x) * (Real.exp ((-(n : ℝ)) * x)))))))
  (h3 : (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ (Set.Icc 0 1))) → (Tendsto (fun n_1 : ℕ => (f (n_1, x))) atTop (𝓝 0)))))
  (h4 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))))
  (h5 : (∫ x in (0 : ℝ)..(1 : ℝ), ((0 : ℝ) * (1 : ℝ))) = 0)
  (h6 : (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))) = 0)
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ))) = ((Real.rpow (n : ℝ) v_uCE_uB1) * (∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((x * (Real.exp ((-(n : ℝ)) * x))) * (1 : ℝ))) = ((((-(1 /. n)) * (Real.exp (-(n : ℝ)))) - ((1 /. (n ^ (2 : ℕ))) * (Real.exp (-(n : ℝ))))) + (1 /. (n ^ (2 : ℕ))))))))
  (h9 : Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (limUnder atTop (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))))))
  (h10 : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 0)))
  (h11 : (v_uCE_uB1 < 2) → (Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))))))
  (h12 : (v_uCE_uB1 ≥ 2) → (Not (Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 0))))
  (h13 : (v_uCE_uB1 ≥ 2) → (Not (Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ)))))))
  (h14 : ∃ L : ℝ, Tendsto (fun n : ℕ => (f (n, x))) atTop (𝓝 L))
  (h15 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow n (v_uCE_uB1 - 2)) * ((1 - (Real.exp (-n))) - (n * (Real.exp (-n)))))) atTop (𝓝 L))
  : (v_uCE_uB1 ∈ ({v_uCE_uB1_1 : ℝ | (v_uCE_uB1_1 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB1_1 < 2)})) ↔ (Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..(1 : ℝ), ((f (n, x)) * (1 : ℝ)))) atTop (𝓝 (∫ x in (0 : ℝ)..(1 : ℝ), (limUnder atTop (fun n : ℕ => (f (n, x))) * (1 : ℝ))))) := by
  sorry

end regenerated_exercise_2802_3_gap_11
