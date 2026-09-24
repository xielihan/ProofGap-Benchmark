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

-- exercise: exercise_1321

theorem proof_gap_exercise_1321_1
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((3 * (Real.tan (4 * x))) - (12 * (Real.tan x))) /. ((3 * (Real.sin (4 * x))) - (12 * (Real.sin x))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))))))))) := by
  sorry

theorem proof_gap_exercise_1321_2
  (h1 : Tendsto (fun x : ℝ => (((3 * (Real.tan (4 * x))) - (12 * (Real.tan x))) /. ((3 * (Real.sin (4 * x))) - (12 * (Real.sin x))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))))))))
  (h2 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))))) (𝓝[≠] 0) (𝓝 L))
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.cos x) ≠ 0)) ∧ ((Real.cos (4 * x)) ≠ 0)) ∧ (((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))) ≠ 0)) → ((((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x)))) = (-(((Real.cos (4 * x)) + (Real.cos x)) /. (((Real.cos x) ^ (2 : ℕ)) * ((Real.cos (4 * x)) ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1321_3
  (h1 : Tendsto (fun x : ℝ => (((3 * (Real.tan (4 * x))) - (12 * (Real.tan x))) /. ((3 * (Real.sin (4 * x))) - (12 * (Real.sin x))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))))))))
  (h2 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.cos x) ≠ 0)) ∧ ((Real.cos (4 * x)) ≠ 0)) ∧ (((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))) ≠ 0)) → ((((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x)))) = (-(((Real.cos (4 * x)) + (Real.cos x)) /. (((Real.cos x) ^ (2 : ℕ)) * ((Real.cos (4 * x)) ^ (2 : ℕ)))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (-(((Real.cos (4 * x)) + (Real.cos x)) /. (((Real.cos x) ^ (2 : ℕ)) * ((Real.cos (4 * x)) ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 (-(2 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1321_4
  (h1 : Tendsto (fun x : ℝ => (((3 * (Real.tan (4 * x))) - (12 * (Real.tan x))) /. ((3 * (Real.sin (4 * x))) - (12 * (Real.sin x))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))))))))
  (h2 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ ((Real.cos x) ≠ 0)) ∧ ((Real.cos (4 * x)) ≠ 0)) ∧ (((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))) ≠ 0)) → ((((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x)))) = (-(((Real.cos (4 * x)) + (Real.cos x)) /. (((Real.cos x) ^ (2 : ℕ)) * ((Real.cos (4 * x)) ^ (2 : ℕ)))))))))
  (h3 : Tendsto (fun x : ℝ => (-(((Real.cos (4 * x)) + (Real.cos x)) /. (((Real.cos x) ^ (2 : ℕ)) * ((Real.cos (4 * x)) ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 (-(2 : ℝ))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((12 * (((1 : ℝ) /. (Real.cos (4 * x))) ^ (2 : ℕ))) - (12 * (((1 : ℝ) /. (Real.cos x)) ^ (2 : ℕ)))) /. ((12 * (Real.cos (4 * x))) - (12 * (Real.cos x))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((3 * (Real.tan (4 * x))) - (12 * (Real.tan x))) /. ((3 * (Real.sin (4 * x))) - (12 * (Real.sin x))))) (𝓝[≠] 0) (𝓝 (-(2 : ℝ))) := by
  sorry
