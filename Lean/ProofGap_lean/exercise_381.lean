import Mathlib

-- exercise: exercise_381
-- Regenerated from proofgap by the current printer.
-- Lean generation failed for gaps: none
-- Last gap: 10; compilation status: passed
-- Classification concerns only the last gap compilation, not every gap below.

-- Source: proofgap/exercise_381/1.txt
namespace regenerated_exercise_381_gap_1

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

theorem proof_gap_exercise_381_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))) := by
  sorry
end regenerated_exercise_381_gap_1

-- Source: proofgap/exercise_381/2.txt
namespace regenerated_exercise_381_gap_2

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

theorem proof_gap_exercise_381_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))) := by
  sorry
end regenerated_exercise_381_gap_2

-- Source: proofgap/exercise_381/3.txt
namespace regenerated_exercise_381_gap_3

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

theorem proof_gap_exercise_381_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  (h4 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)))) → (|((f x))| ≤ M))))))))) := by
  sorry
end regenerated_exercise_381_gap_3

-- Source: proofgap/exercise_381/4.txt
namespace regenerated_exercise_381_gap_4

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

theorem proof_gap_exercise_381_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  (h4 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h5 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)))) → (|((f x))| ≤ M))))))))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x = (k /. n))) ∧ ((Int.gcd k (n : ℤ)) = 1)) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))) := by
  sorry
end regenerated_exercise_381_gap_4

-- Source: proofgap/exercise_381/5.txt
namespace regenerated_exercise_381_gap_5

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

theorem proof_gap_exercise_381_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  (h4 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h5 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)))) → (|((f x))| ≤ M))))))))))
  (h6 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x = (k /. n))) ∧ ((Int.gcd k (n : ℤ)) = 1)) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((x_0_1 - v_uCE_uB4_1) * ⌊M⌋) < k)) ∧ (k < ((x_0_1 + v_uCE_uB4_1) * ⌊M⌋))) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))) := by
  sorry
end regenerated_exercise_381_gap_5

-- Source: proofgap/exercise_381/6.txt
namespace regenerated_exercise_381_gap_6

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

theorem proof_gap_exercise_381_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), ((((m ∈ (Set.univ : Set ℤ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  (h4 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h5 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)))) → (|((f x))| ≤ M))))))))))
  (h6 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), ((((((k ∈ (Set.univ : Set ℤ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x = (k /. n))) ∧ ((Int.gcd k (n : ℤ)) = 1)) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h7 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), ((((((k ∈ (Set.univ : Set ℤ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((x_0 - v_uCE_uB4) * ⌊M⌋) < k)) ∧ (k < ((x_0 + v_uCE_uB4) * ⌊M⌋))) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (Set.Finite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))) := by
  sorry
end regenerated_exercise_381_gap_6

-- Source: proofgap/exercise_381/7.txt
namespace regenerated_exercise_381_gap_7

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

theorem proof_gap_exercise_381_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  (h4 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h5 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)))) → (|((f x))| ≤ M))))))))))
  (h6 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x = (k /. n))) ∧ ((Int.gcd k (n : ℤ)) = 1)) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h7 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((x_0_1 - v_uCE_uB4_1) * ⌊M⌋) < k)) ∧ (k < ((x_0_1 + v_uCE_uB4_1) * ⌊M⌋))) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h8 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (Set.Finite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → False)))) := by
  sorry
end regenerated_exercise_381_gap_7

-- Source: proofgap/exercise_381/8.txt
namespace regenerated_exercise_381_gap_8

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

theorem proof_gap_exercise_381_8
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  (h4 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h5 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)))) → (|((f x))| ≤ M))))))))))
  (h6 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x = (k /. n))) ∧ ((Int.gcd k (n : ℤ)) = 1)) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h7 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((x_0_1 - v_uCE_uB4_1) * ⌊M⌋) < k)) ∧ (k < ((x_0_1 + v_uCE_uB4_1) * ⌊M⌋))) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h8 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (Set.Finite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h9 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → False)))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Not (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))))))) := by
  sorry
end regenerated_exercise_381_gap_8

-- Source: proofgap/exercise_381/9.txt
namespace regenerated_exercise_381_gap_9

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

theorem proof_gap_exercise_381_9
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  (h4 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h5 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)))) → (|((f x))| ≤ M))))))))))
  (h6 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x = (k /. n))) ∧ ((Int.gcd k (n : ℤ)) = 1)) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h7 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((x_0_1 - v_uCE_uB4_1) * ⌊M⌋) < k)) ∧ (k < ((x_0_1 + v_uCE_uB4_1) * ⌊M⌋))) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h8 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (Set.Finite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h9 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → False)))))
  (h10 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Not (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))))))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (((f x_0) ∈ (Set.univ : Set ℝ)) ∧ (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Not (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)))))))))) := by
  sorry
end regenerated_exercise_381_gap_9

-- Source: proofgap/exercise_381/10.txt
namespace regenerated_exercise_381_gap_10

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

theorem proof_gap_exercise_381_10
  (f : (ℝ -> ℝ))
  (h1 : (forall (m : ℤ) (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((Int.gcd m (n : ℤ)) = 1)) → ((f (m /. n)) = n))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∉ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))) → ((f x) = 0))))
  (h3 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → ((f x_0) ∈ (Set.univ : Set ℝ)))))
  (h4 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Set.Infinite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h5 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)))) → (|((f x))| ≤ M))))))))))
  (h6 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x = (k /. n))) ∧ ((Int.gcd k (n : ℤ)) = 1)) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h7 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 0)) ∧ (forall (x : ℝ) (x_0_1 : ℝ) (v_uCE_uB4_1 : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x_0_1 ∈ (Set.univ : Set ℝ))) ∧ (v_uCE_uB4_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ ((Set.Ioo (x_0_1 - v_uCE_uB4_1) (x_0_1 + v_uCE_uB4_1)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1})))) → (exists (k : ℤ) (n : ℕ), (((((((n ∈ (Set.univ : Set ℕ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((x_0_1 - v_uCE_uB4_1) * ⌊M⌋) < k)) ∧ (k < ((x_0_1 + v_uCE_uB4_1) * ⌊M⌋))) ∧ (1 ≤ n)) ∧ (n ≤ ⌊M⌋))))))))))))
  (h8 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → (Set.Finite ((Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)) ∩ ({x_1 : ℝ | ∃ q : ℚ, (q : ℝ) = x_1}))))))))
  (h9 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), ((((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) ∧ (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))) → False)))))
  (h10 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Not (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4))))))))))
  (h11 : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (((f x_0) ∈ (Set.univ : Set ℝ)) ∧ (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Not (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)))))))))))
  : (forall (x_0 : ℝ), ((x_0 ∈ (Set.univ : Set ℝ)) → (((f x_0) ∈ (Set.univ : Set ℝ)) ∧ (forall (v_uCE_uB4 : ℝ), (((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB4 > 0)) → (Not (Bornology.IsBounded (f '' (Set.Ioo (x_0 - v_uCE_uB4) (x_0 + v_uCE_uB4)))))))))) := by
  sorry
end regenerated_exercise_381_gap_10

