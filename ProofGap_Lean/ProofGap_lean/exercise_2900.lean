import Mathlib

-- exercise: exercise_2900
-- Regenerated for Lean 4.29.0-rc6 / Mathlib 5c8398d.

-- Source: proofgap/exercise_2900/1.txt
namespace regenerated_exercise_2900_gap_1

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

theorem proof_gap_exercise_2900_1
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))) := by
  sorry

end regenerated_exercise_2900_gap_1

-- Source: proofgap/exercise_2900/2.txt
namespace regenerated_exercise_2900_gap_2

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

theorem proof_gap_exercise_2900_2
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) := by
  sorry

end regenerated_exercise_2900_gap_2

-- Source: proofgap/exercise_2900/3.txt
namespace regenerated_exercise_2900_gap_3

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

theorem proof_gap_exercise_2900_3
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S) := by
  sorry

end regenerated_exercise_2900_gap_3

-- Source: proofgap/exercise_2900/4.txt
namespace regenerated_exercise_2900_gap_4

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

theorem proof_gap_exercise_2900_4
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S) := by
  sorry

end regenerated_exercise_2900_gap_4

-- Source: proofgap/exercise_2900/5.txt
namespace regenerated_exercise_2900_gap_5

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

theorem proof_gap_exercise_2900_5
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤) := by
  sorry

end regenerated_exercise_2900_gap_5

-- Source: proofgap/exercise_2900/6.txt
namespace regenerated_exercise_2900_gap_6

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

theorem proof_gap_exercise_2900_6
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))) := by
  sorry

end regenerated_exercise_2900_gap_6

-- Source: proofgap/exercise_2900/7.txt
namespace regenerated_exercise_2900_gap_7

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

theorem proof_gap_exercise_2900_7
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))) := by
  sorry

end regenerated_exercise_2900_gap_7

-- Source: proofgap/exercise_2900/8.txt
namespace regenerated_exercise_2900_gap_8

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

theorem proof_gap_exercise_2900_8
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))) := by
  sorry

end regenerated_exercise_2900_gap_8

-- Source: proofgap/exercise_2900/9.txt
namespace regenerated_exercise_2900_gap_9

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

theorem proof_gap_exercise_2900_9
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  (h15 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 L) ∧ (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) > A)))))) := by
  sorry

end regenerated_exercise_2900_gap_9

-- Source: proofgap/exercise_2900/10.txt
namespace regenerated_exercise_2900_gap_10

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

theorem proof_gap_exercise_2900_10
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  (h15 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))))
  (h16 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 L) ∧ (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) > A)))))))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0) ≥ (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))))))))) := by
  sorry

end regenerated_exercise_2900_gap_10

-- Source: proofgap/exercise_2900/11.txt
namespace regenerated_exercise_2900_gap_11

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

theorem proof_gap_exercise_2900_11
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  (h15 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))))
  (h16 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 L) ∧ (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) > A)))))))
  (h17 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0) ≥ (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))))))))))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 L) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) > A)))) := by
  sorry

end regenerated_exercise_2900_gap_11

-- Source: proofgap/exercise_2900/12.txt
namespace regenerated_exercise_2900_gap_12

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

theorem proof_gap_exercise_2900_12
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  (h15 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))))
  (h16 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 L) ∧ (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) > A)))))))
  (h17 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0) ≥ (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))))))))))
  (h18 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 L) ∧ (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) > A)))))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (A > S))) := by
  sorry

end regenerated_exercise_2900_gap_12

-- Source: proofgap/exercise_2900/13.txt
namespace regenerated_exercise_2900_gap_13

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

theorem proof_gap_exercise_2900_13
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  (h15 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))))
  (h16 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 L) ∧ (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) > A)))))))
  (h17 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0) ≥ (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))))))))))
  (h18 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 L) ∧ (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) > A)))))
  (h19 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (A > S))))
  : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → False)) := by
  sorry

end regenerated_exercise_2900_gap_13

-- Source: proofgap/exercise_2900/14.txt
namespace regenerated_exercise_2900_gap_14

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

theorem proof_gap_exercise_2900_14
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  (h15 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))))
  (h16 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 L) ∧ (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) > A)))))))
  (h17 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0) ≥ (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))))))))))
  (h18 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 L) ∧ (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) > A)))))
  (h19 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (A > S))))
  (h20 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → False)))
  : Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) := by
  sorry

end regenerated_exercise_2900_gap_14

-- Source: proofgap/exercise_2900/15.txt
namespace regenerated_exercise_2900_gap_15

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

theorem proof_gap_exercise_2900_15
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  (h15 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))))
  (h16 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 L) ∧ (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) > A)))))))
  (h17 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0) ≥ (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))))))))))
  (h18 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 L) ∧ (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) > A)))))
  (h19 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (A > S))))
  (h20 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → False)))
  (h21 : Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0))
  : HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S := by
  sorry

end regenerated_exercise_2900_gap_15

-- Source: proofgap/exercise_2900/16.txt
namespace regenerated_exercise_2900_gap_16

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

theorem proof_gap_exercise_2900_16
  (a : (ℕ -> ℝ))
  (f : (ℝ -> ℝ))
  (R : ℝ)
  (S : ℝ)
  (x : ℝ)
  (n : ℕ)
  (h1 : (R ∈ (Set.univ : Set ℝ)) ∧ (R > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : n ∈ (Set.univ : Set ℕ))
  (h5 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → ((a n_1) ≥ 0))))
  (h6 : (forall (x_1 : ℝ), ((((x_1 ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ x_1)) ∧ (x_1 < R)) → ((f x_1) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)))))
  (h7 : Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 S))
  (h8 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 (f R))))
  (h9 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((f R) = (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)))
  (h10 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) = S))
  (h11 : (Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S))
  (h12 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → ((((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) : ℝ) : EReal) = ⊤))
  (h13 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), ((((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A)) ∧ (A > S))))))
  (h14 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))))))))))
  (h15 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ ((∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (R ^ n_1))) > A))))))
  (h16 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) (𝓝[<] R) (𝓝 L) ∧ (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))) > A)))))))
  (h17 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 0)) → ((∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0) ≥ (∑ n_1 ∈ Finset.Icc (0 : ℕ) N, ((a n_1) * (x_1 ^ n_1)))))))))))
  (h18 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) (𝓝[<] R) (𝓝 L) ∧ (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (limUnder (𝓝[<] R) (fun x_1 : ℝ => (∑' n_1, if (0 : ℕ) ≤ n_1 then ((a n_1) * (x_1 ^ n_1)) else 0)) > A)))))
  (h19 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → (A > S))))
  (h20 : (¬ Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0)) → (forall (A : ℝ), (((A ∈ (Set.univ : Set ℝ)) ∧ (A > S)) → False)))
  (h21 : Summable (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0))
  (h22 : HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S)
  : HasSum (fun (n_1 : ℕ) => if (0 : ℕ) ≤ n_1 then ((a n_1) * (R ^ n_1)) else 0) S := by
  sorry

end regenerated_exercise_2900_gap_16
