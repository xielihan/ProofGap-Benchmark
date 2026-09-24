import Mathlib

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

-- exercise: exercise_515

theorem proof_gap_exercise_515_1
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a ≠ 0)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a)) → ((Real.rpow ((x + a) /. (x - a)) x) = (Real.rpow (1 + (1 /. ((x - a) /. (2 * a)))) (((((x - a) /. (2 * a)) * 2) * a) + a))))) := by
  sorry

theorem proof_gap_exercise_515_2
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a ≠ 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a)) → ((Real.rpow ((x + a) /. (x - a)) x) = (Real.rpow (1 + (1 /. ((x - a) /. (2 * a)))) (((((x - a) /. (2 * a)) * 2) * a) + a))))))
  : Tendsto (fun t : ℝ => (Real.rpow (1 + t) (1 /. t))) (𝓝[≠] 0) (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_515_3
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a ≠ 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a)) → ((Real.rpow ((x + a) /. (x - a)) x) = (Real.rpow (1 + (1 /. ((x - a) /. (2 * a)))) (((((x - a) /. (2 * a)) * 2) * a) + a))))))
  (h4 : Tendsto (fun t : ℝ => (Real.rpow (1 + t) (1 /. t))) (𝓝[≠] 0) (𝓝 (Real.exp 1)))
  : Tendsto (fun u : ℝ => (Real.rpow (1 + (1 /. u)) u)) atTop (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_515_4
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a ≠ 0)
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a)) → ((Real.rpow ((x + a) /. (x - a)) x) = (Real.rpow (1 + (1 /. ((x - a) /. (2 * a)))) (((((x - a) /. (2 * a)) * 2) * a) + a))))))
  (h4 : Tendsto (fun t : ℝ => (Real.rpow (1 + t) (1 /. t))) (𝓝[≠] 0) (𝓝 (Real.exp 1)))
  (h5 : Tendsto (fun u : ℝ => (Real.rpow (1 + (1 /. u)) u)) atTop (𝓝 (Real.exp 1)))
  : Tendsto (fun x : ℝ => (Real.rpow ((x + a) /. (x - a)) x)) atTop (𝓝 (Real.exp (2 * a))) := by
  sorry
