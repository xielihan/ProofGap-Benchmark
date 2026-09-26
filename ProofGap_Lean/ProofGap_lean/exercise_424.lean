import Mathlib

-- exercise: exercise_424
-- Regenerated for Lean 4.29.0-rc6 / Mathlib 5c8398d.

-- Source: proofgap/exercise_424/1.txt
namespace regenerated_exercise_424_gap_1

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

theorem proof_gap_exercise_424_1
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1))))) := by
  sorry

end regenerated_exercise_424_gap_1

-- Source: proofgap/exercise_424/2.txt
namespace regenerated_exercise_424_gap_2

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

theorem proof_gap_exercise_424_2
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1)) = ((x - 1) * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k))))))) := by
  sorry

end regenerated_exercise_424_gap_2

-- Source: proofgap/exercise_424/3.txt
namespace regenerated_exercise_424_gap_3

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

theorem proof_gap_exercise_424_3
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1)) = ((x - 1) * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))) (𝓝[≠] 1) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) /. (x - 1))) (𝓝[≠] 1) (𝓝 (limUnder (𝓝[≠] 1) (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))))))) := by
  sorry

end regenerated_exercise_424_gap_3

-- Source: proofgap/exercise_424/4.txt
namespace regenerated_exercise_424_gap_4

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

theorem proof_gap_exercise_424_4
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1)) = ((x - 1) * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k))))))))
  (h5 : Tendsto (fun x : ℝ => (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) /. (x - 1))) (𝓝[≠] 1) (𝓝 (limUnder (𝓝[≠] 1) (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))) (𝓝[≠] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))) (𝓝[≠] 1) (𝓝 (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (n - k))) := by
  sorry

end regenerated_exercise_424_gap_4

-- Source: proofgap/exercise_424/5.txt
namespace regenerated_exercise_424_gap_5

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

theorem proof_gap_exercise_424_5
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1)) = ((x - 1) * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k))))))))
  (h5 : Tendsto (fun x : ℝ => (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) /. (x - 1))) (𝓝[≠] 1) (𝓝 (limUnder (𝓝[≠] 1) (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))))))
  (h6 : Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))) (𝓝[≠] 1) (𝓝 (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (n - k))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))) (𝓝[≠] 1) (𝓝 L))
  : (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (n - k)) = ((n * (n + 1)) /. 2) := by
  sorry

end regenerated_exercise_424_gap_5

-- Source: proofgap/exercise_424/6.txt
namespace regenerated_exercise_424_gap_6

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

theorem proof_gap_exercise_424_6
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) = (∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((∑ i ∈ Finset.Icc (1 : ℕ) n, ((x ^ i) - 1)) = ((x - 1) * (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k))))))))
  (h5 : Tendsto (fun x : ℝ => (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) /. (x - 1))) (𝓝[≠] 1) (𝓝 (limUnder (𝓝[≠] 1) (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))))))
  (h6 : Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))) (𝓝[≠] 1) (𝓝 (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (n - k))))
  (h7 : (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), (n - k)) = ((n * (n + 1)) /. 2))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc (0 : ℕ) (n - 1), ((n - k) * (x ^ k)))) (𝓝[≠] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (((∑ i ∈ Finset.Icc (1 : ℕ) n, (x ^ i)) - n) /. (x - 1))) (𝓝[≠] 1) (𝓝 ((n * (n + 1)) /. 2)) := by
  sorry

end regenerated_exercise_424_gap_6
