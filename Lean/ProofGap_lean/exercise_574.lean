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

-- exercise: exercise_574

theorem proof_gap_exercise_574_1
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow ((1 + 1) - x) (((1 /. (1 - x)) * ((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2)))) * (2 /. Real.pi)))) (𝓝[≠] 1) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (Real.rpow (2 - x) ((1 : ℝ) /. (Real.cos ((Real.pi * x) /. 2))))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => (Real.rpow ((1 + 1) - x) (((1 /. (1 - x)) * ((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2)))) * (2 /. Real.pi)))))))) := by
  sorry

theorem proof_gap_exercise_574_2
  (h1 : Tendsto (fun x : ℝ => (Real.rpow (2 - x) ((1 : ℝ) /. (Real.cos ((Real.pi * x) /. 2))))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => (Real.rpow ((1 + 1) - x) (((1 /. (1 - x)) * ((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2)))) * (1 /. Real.pi)))))))
  (h2 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow ((1 + 1) - x) (((1 /. (1 - x)) * ((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2)))) * (1 /. Real.pi)))) (𝓝[≠] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow ((1 + 1) - x) (1 /. (1 - x)))) (𝓝[≠] 1) (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_574_3
  (h1 : Tendsto (fun x : ℝ => (Real.rpow (2 - x) ((1 : ℝ) /. (Real.cos ((Real.pi * x) /. 2))))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => (Real.rpow ((1 + 1) - x) (((1 /. (1 - x)) * ((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2)))) * (2 /. Real.pi)))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow ((1 + 1) - x) (1 /. (1 - x)))) (𝓝[≠] 1) (𝓝 (Real.exp 1)))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow ((1 + 1) - x) (((1 /. (1 - x)) * ((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2)))) * (2 /. Real.pi)))) (𝓝[≠] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2))) * (2 /. Real.pi))) (𝓝[≠] 1) (𝓝 (2 /. Real.pi)) := by
  sorry

theorem proof_gap_exercise_574_4
  (h1 : Tendsto (fun x : ℝ => (Real.rpow (2 - x) ((1 : ℝ) /. (Real.cos ((Real.pi * x) /. 2))))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => (Real.rpow ((1 + 1) - x) (((1 /. (1 - x)) * ((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2)))) * (2 /. Real.pi)))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow ((1 + 1) - x) (1 /. (1 - x)))) (𝓝[≠] 1) (𝓝 (Real.exp 1)))
  (h3 : Tendsto (fun x : ℝ => (((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2))) * (2 /. Real.pi))) (𝓝[≠] 1) (𝓝 (2 /. Real.pi)))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow ((1 + 1) - x) (((1 /. (1 - x)) * ((Real.pi * (x - 1)) /. (Real.sin ((Real.pi * (x - 1)) /. 2)))) * (2 /. Real.pi)))) (𝓝[≠] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow (2 - x) ((1 : ℝ) /. (Real.cos ((Real.pi * x) /. 2))))) (𝓝[≠] 1) (𝓝 (Real.exp (2 /. Real.pi))) := by
  sorry
