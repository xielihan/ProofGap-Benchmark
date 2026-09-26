import Mathlib

-- exercise: exercise_2787
-- Regenerated for Lean 4.29.0-rc6 / Mathlib 5c8398d.

-- Source: proofgap/exercise_2787/1.txt
namespace regenerated_exercise_2787_gap_1

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

theorem proof_gap_exercise_2787_1
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))) := by
  sorry

end regenerated_exercise_2787_gap_1

-- Source: proofgap/exercise_2787/2.txt
namespace regenerated_exercise_2787_gap_2

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

theorem proof_gap_exercise_2787_2
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  (h11 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))))
  : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (A n_1) else 0) := by
  sorry

end regenerated_exercise_2787_gap_2

-- Source: proofgap/exercise_2787/3.txt
namespace regenerated_exercise_2787_gap_3

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

theorem proof_gap_exercise_2787_3
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  (h11 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))))
  (h12 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (A n_1) else 0))
  : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (max |((phi (n_1, a)))| |((phi (n_1, b)))|)))))) := by
  sorry

end regenerated_exercise_2787_gap_3

-- Source: proofgap/exercise_2787/4.txt
namespace regenerated_exercise_2787_gap_4

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

theorem proof_gap_exercise_2787_4
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  (h11 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))))
  (h12 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (A n_1) else 0))
  (h13 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (max |((phi (n_1, a)))| |((phi (n_1, b)))|)))))))
  : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (A n_1)))))) := by
  sorry

end regenerated_exercise_2787_gap_4

-- Source: proofgap/exercise_2787/5.txt
namespace regenerated_exercise_2787_gap_5

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

theorem proof_gap_exercise_2787_5
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  (h11 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))))
  (h12 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (A n_1) else 0))
  (h13 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (max |((phi (n_1, a)))| |((phi (n_1, b)))|)))))))
  (h14 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (A n_1)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))) := by
  sorry

end regenerated_exercise_2787_gap_5

-- Source: proofgap/exercise_2787/6.txt
namespace regenerated_exercise_2787_gap_6

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

theorem proof_gap_exercise_2787_6
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  (h11 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))))
  (h12 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (A n_1) else 0))
  (h13 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (max |((phi (n_1, a)))| |((phi (n_1, b)))|)))))))
  (h14 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (A n_1)))))))
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (phi (k_1, x))))| < v_uCE_uB5))))))) := by
  sorry

end regenerated_exercise_2787_gap_6

-- Source: proofgap/exercise_2787/7.txt
namespace regenerated_exercise_2787_gap_7

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

theorem proof_gap_exercise_2787_7
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  (h11 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))))
  (h12 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (A n_1) else 0))
  (h13 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (max |((phi (n_1, a)))| |((phi (n_1, b)))|)))))))
  (h14 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (A n_1)))))))
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))))
  (h16 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (phi (k_1, x))))| < v_uCE_uB5))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))) := by
  sorry

end regenerated_exercise_2787_gap_7

-- Source: proofgap/exercise_2787/8.txt
namespace regenerated_exercise_2787_gap_8

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

theorem proof_gap_exercise_2787_8
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  (h11 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))))
  (h12 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (A n_1) else 0))
  (h13 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (max |((phi (n_1, a)))| |((phi (n_1, b)))|)))))))
  (h14 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (A n_1)))))))
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))))
  (h16 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (phi (k_1, x))))| < v_uCE_uB5))))))))
  (h17 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (phi (k_1, x))))| < v_uCE_uB5))))))) := by
  sorry

end regenerated_exercise_2787_gap_8

-- Source: proofgap/exercise_2787/9.txt
namespace regenerated_exercise_2787_gap_9

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

theorem proof_gap_exercise_2787_9
  (phi : (ℕ × ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (n : ℕ)
  (k : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : k ∈ (Set.univ : Set ℕ))
  (h5 : a < b)
  (h6 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → ((phi (n_1, x)) ∈ (Set.univ : Set ℝ)))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (MonotoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b))) ∨ (let _ : ((Set.Icc a b)) ⊆ ({ x_1 : ℝ | ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Icc a b))) }) := (by intro x hx; simpa only [Set.mem_setOf_eq, Set.mem_univ, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_prod, true_and, and_true, and_assoc, and_left_comm, and_comm] using hx); (AntitoneOn (fun (x : ℝ) => (phi (n_1, x))) (Set.Icc a b)))))))
  (h8 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, a)))| else 0))
  (h9 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then |((phi (n_1, b)))| else 0))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((A : ℕ → _) n_1) = (max |((phi (n_1, a)))| |((phi (n_1, b)))|))))
  (h11 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((0 ≤ (A n_1)) ∧ ((A n_1) ≤ (|((phi (n_1, a)))| + |((phi (n_1, b)))|))))))
  (h12 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (A n_1) else 0))
  (h13 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (max |((phi (n_1, a)))| |((phi (n_1, b)))|)))))))
  (h14 : (forall (n_1 : ℕ), ((n_1 ∈ (Set.univ : Set ℕ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) → (|((phi (n_1, x)))| ≤ (A n_1)))))))
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))))
  (h16 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (phi (k_1, x))))| < v_uCE_uB5))))))))
  (h17 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))))
  (h18 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (phi (k_1, x))))| < v_uCE_uB5))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc a b))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then ‖((phi (n_1, x)))‖ else 0)))) ∧ (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n_1 : ℕ) (p : ℕ) (x : ℝ), ((((((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (p ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (p ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Icc a b))) ∧ (n_1 > N)) → (|((∑ k_1 ∈ Finset.Icc (n_1 + 1) (n_1 + p), (phi (k_1, x))))| < v_uCE_uB5))))))) := by
  sorry

end regenerated_exercise_2787_gap_9
