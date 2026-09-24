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

-- exercise: exercise_1358

theorem proof_gap_exercise_1358_1
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : x > 0)
  (h5 : x ≠ a)
  : (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) * (Real.log a)) - (a * (Real.rpow x_1 (a - 1))))) (𝓝[≠] a) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) - (Real.rpow x_1 a)) /. (x_1 - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x_1 : ℝ => (((Real.rpow a x_1) * (Real.log a)) - (a * (Real.rpow x_1 (a - 1))))))))) := by
  sorry

theorem proof_gap_exercise_1358_2
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : x > 0)
  (h5 : x ≠ a)
  (h6 : Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) - (Real.rpow x_1 a)) /. (x_1 - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x_1 : ℝ => (((Real.rpow a x_1) * (Real.log a)) - (a * (Real.rpow x_1 (a - 1))))))))
  (h7 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) * (Real.log a)) - (a * (Real.rpow x_1 (a - 1))))) (𝓝[≠] a) (𝓝 L))
  : Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) * (Real.log a)) - (a * (Real.rpow x_1 (a - 1))))) (𝓝[≠] a) (𝓝 ((Real.rpow a a) * ((Real.log a) - 1))) := by
  sorry

theorem proof_gap_exercise_1358_3
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : x > 0)
  (h5 : x ≠ a)
  (h6 : Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) - (Real.rpow x_1 a)) /. (x_1 - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x_1 : ℝ => (((Real.rpow a x_1) * (Real.log a)) - (a * (Real.rpow x_1 (a - 1))))))))
  (h7 : Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) * (Real.log a)) - (a * (Real.rpow x_1 (a - 1))))) (𝓝[≠] a) (𝓝 ((Real.rpow a a) * ((Real.log a) - 1))))
  (h8 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) * (Real.log a)) - (a * (Real.rpow x_1 (a - 1))))) (𝓝[≠] a) (𝓝 L))
  : Tendsto (fun x_1 : ℝ => (((Real.rpow a x_1) - (Real.rpow x_1 a)) /. (x_1 - a))) (𝓝[≠] a) (𝓝 ((Real.rpow a a) * ((Real.log a) - 1))) := by
  sorry
