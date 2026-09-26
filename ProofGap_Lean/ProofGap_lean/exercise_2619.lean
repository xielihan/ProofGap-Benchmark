import Mathlib

-- exercise: exercise_2619
-- Regenerated for Lean 4.29.0-rc6 / Mathlib 5c8398d.

-- Source: proofgap/exercise_2619/1.txt
namespace regenerated_exercise_2619_gap_1

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

theorem proof_gap_exercise_2619_1
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : True)
  (h2 : p ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → ((a n) = (1 /. (n * (Real.rpow (Real.log (n : ℝ)) p)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((1 /. (x * (Real.rpow (Real.log x) p))) ≥ 0))) := by
  sorry

end regenerated_exercise_2619_gap_1

-- Source: proofgap/exercise_2619/2.txt
namespace regenerated_exercise_2619_gap_2

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

theorem proof_gap_exercise_2619_2
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : True)
  (h2 : p ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → ((a n) = (1 /. (n * (Real.rpow (Real.log (n : ℝ)) p)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((1 /. (x * (Real.rpow (Real.log x) p))) ≥ 0))))
  : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 1)) ∧ (AntitoneOn (fun (x : ℝ) => (1 /. (x * (Real.rpow (Real.log x) p)))) (Set.Ici M)))) := by
  sorry

end regenerated_exercise_2619_gap_2

-- Source: proofgap/exercise_2619/3.txt
namespace regenerated_exercise_2619_gap_3

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

theorem proof_gap_exercise_2619_3
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : True)
  (h2 : p ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → ((a n) = (1 /. (n * (Real.rpow (Real.log (n : ℝ)) p)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((1 /. (x * (Real.rpow (Real.log x) p))) ≥ 0))))
  (h5 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 1)) ∧ (AntitoneOn (fun (x : ℝ) => (1 /. (x * (Real.rpow (Real.log x) p)))) (Set.Ici M)))))
  : (Filter.Eventually (fun x_1 : ℝ => ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 2))) atTop ∧ ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (1 /. ((1 - p) * (Real.rpow (Real.log x_1) (p - 1))))) atTop (𝓝 L) ∧ Filter.Eventually (fun x_1 : ℝ => ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 2))) atTop ∧ ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.log x_1))) atTop (𝓝 L) ∧ ((∫ x in Set.Ioi (2 : ℝ), (((1 : ℝ) /. (x * (Real.rpow (Real.log x) p))) * (1 : ℝ))) = (if (p ≠ 1) then ((limUnder atTop (fun x_1 : ℝ => (1 /. ((1 - p) * (Real.rpow (Real.log x_1) (p - 1)))))) - (1 /. ((1 - p) * (Real.rpow (Real.log (2 : ℝ)) (p - 1))))) else (if (p = 1) then ((limUnder atTop (fun x_1 : ℝ => (Real.log (Real.log x_1)))) - (Real.log (Real.log (2 : ℝ)))) else ((limUnder atTop (fun x_1 : ℝ => (Real.log (Real.log x_1)))) - (Real.log (Real.log (2 : ℝ)))))))) := by
  sorry

end regenerated_exercise_2619_gap_3

-- Source: proofgap/exercise_2619/4.txt
namespace regenerated_exercise_2619_gap_4

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

theorem proof_gap_exercise_2619_4
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : True)
  (h2 : p ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → ((a n) = (1 /. (n * (Real.rpow (Real.log (n : ℝ)) p)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((1 /. (x * (Real.rpow (Real.log x) p))) ≥ 0))))
  (h5 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 1)) ∧ (AntitoneOn (fun (x : ℝ) => (1 /. (x * (Real.rpow (Real.log x) p)))) (Set.Ici M)))))
  (h6 : (∫ x in Set.Ioi (2 : ℝ), (((1 : ℝ) /. (x * (Real.rpow (Real.log x) p))) * (1 : ℝ))) = (if (p ≠ 1) then ((limUnder atTop (fun x_1 : ℝ => (1 /. ((1 - p) * (Real.rpow (Real.log x_1) (p - 1)))))) - (1 /. ((1 - p) * (Real.rpow (Real.log (2 : ℝ)) (p - 1))))) else (if (p = 1) then ((limUnder atTop (fun x_1 : ℝ => (Real.log (Real.log x_1)))) - (Real.log (Real.log (2 : ℝ)))) else ((limUnder atTop (fun x_1 : ℝ => (Real.log (Real.log x_1)))) - (Real.log (Real.log (2 : ℝ)))))))
  (h7 : Filter.Eventually (fun x_1 : ℝ => ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 2))) atTop)
  (h8 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (1 /. ((1 - p) * (Real.rpow (Real.log x_1) (p - 1))))) atTop (𝓝 L))
  (h9 : Filter.Eventually (fun x_1 : ℝ => ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 2))) atTop)
  (h10 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.log x_1))) atTop (𝓝 L))
  : (Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (a n) else 0)) ↔ (p > 1) := by
  sorry

end regenerated_exercise_2619_gap_4

-- Source: proofgap/exercise_2619/5.txt
namespace regenerated_exercise_2619_gap_5

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

theorem proof_gap_exercise_2619_5
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : True)
  (h2 : p ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 2)) → ((a n) = (1 /. (n * (Real.rpow (Real.log (n : ℝ)) p)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 1)) → ((1 /. (x * (Real.rpow (Real.log x) p))) ≥ 0))))
  (h5 : (exists (M : ℝ), (((M ∈ (Set.univ : Set ℝ)) ∧ (M > 1)) ∧ (AntitoneOn (fun (x : ℝ) => (1 /. (x * (Real.rpow (Real.log x) p)))) (Set.Ici M)))))
  (h6 : (∫ x in Set.Ioi (2 : ℝ), (((1 : ℝ) /. (x * (Real.rpow (Real.log x) p))) * (1 : ℝ))) = (if (p ≠ 1) then ((limUnder atTop (fun x_1 : ℝ => (1 /. ((1 - p) * (Real.rpow (Real.log x_1) (p - 1)))))) - (1 /. ((1 - p) * (Real.rpow (Real.log (2 : ℝ)) (p - 1))))) else (if (p = 1) then ((limUnder atTop (fun x_1 : ℝ => (Real.log (Real.log x_1)))) - (Real.log (Real.log (2 : ℝ)))) else ((limUnder atTop (fun x_1 : ℝ => (Real.log (Real.log x_1)))) - (Real.log (Real.log (2 : ℝ)))))))
  (h7 : (Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (a n) else 0)) ↔ (p > 1))
  (h8 : Filter.Eventually (fun x_1 : ℝ => ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 2))) atTop)
  (h9 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (1 /. ((1 - p) * (Real.rpow (Real.log x_1) (p - 1))))) atTop (𝓝 L))
  (h10 : Filter.Eventually (fun x_1 : ℝ => ((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≥ 2))) atTop)
  (h11 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.log x_1))) atTop (𝓝 L))
  : (p ∈ ({p_1 : ℝ | (p_1 ∈ (Set.univ : Set ℝ)) ∧ (p_1 > 1)})) ↔ (Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

end regenerated_exercise_2619_gap_5
