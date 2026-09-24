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

-- exercise: exercise_527

theorem proof_gap_exercise_527_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  : (x ≠ (-(1 : ℝ))) → (∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (1 /. ((n - 1) /. (x + 1)))) ((((n - 1) /. (x + 1)) * (x + 1)) + 1))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (Real.rpow ((n + x) /. (n - 1)) n)) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (1 /. ((n - 1) /. (x + 1)))) ((((n - 1) /. (x + 1)) * (x + 1)) + 1))))))) := by
  sorry

theorem proof_gap_exercise_527_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (x ≠ (-(1 : ℝ))) → (Tendsto (fun n : ℕ => (Real.rpow ((n + x) /. (n - 1)) n)) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (1 /. ((n - 1) /. (x + 1)))) ((((n - 1) /. (x + 1)) * (x + 1)) + 1)))))))
  (h3 : x ≠ (-(1 : ℝ)))
  (h4 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (1 /. ((n - 1) /. (x + 1)))) ((((n - 1) /. (x + 1)) * (x + 1)) + 1))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (Real.rpow (1 + (1 /. ((n - 1) /. (x + 1)))) ((((n - 1) /. (x + 1)) * (x + 1)) + 1))) atTop (𝓝 (Real.exp (x + 1))) := by
  sorry

theorem proof_gap_exercise_527_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (x ≠ (-(1 : ℝ))) → (Tendsto (fun n : ℕ => (Real.rpow ((n + x) /. (n - 1)) n)) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (Real.rpow (1 + (1 /. ((n - 1) /. (x + 1)))) ((((n - 1) /. (x + 1)) * (x + 1)) + 1)))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (1 + (1 /. ((n - 1) /. (x + 1)))) ((((n - 1) /. (x + 1)) * (x + 1)) + 1))) atTop (𝓝 (Real.exp (x + 1))))
  (h4 : x ≠ (-(1 : ℝ)))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.rpow (1 + (1 /. ((n - 1) /. (x + 1)))) ((((n - 1) /. (x + 1)) * (x + 1)) + 1))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (Real.rpow ((n + x) /. (n - 1)) n)) atTop (𝓝 (Real.exp (x + 1))) := by
  sorry
