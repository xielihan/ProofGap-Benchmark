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

-- exercise: exercise_524

theorem proof_gap_exercise_524_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(Real.pi /. 4)) (Real.pi /. 4)))) ∧ (x ≠ 0)) → (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow ((1 - (Real.tan x_1)) /. (1 + (Real.tan x_1))) ((1 : ℝ) /. (Real.tan x_1)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.tan ((Real.pi /. 4) - x_1)) ((1 : ℝ) /. (Real.tan x_1)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x_1 : ℝ => (Real.rpow ((1 - (Real.tan x_1)) /. (1 + (Real.tan x_1))) ((1 : ℝ) /. (Real.tan x_1)))))))))) := by
  sorry

theorem proof_gap_exercise_524_2
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow ((1 - (Real.tan x_1)) /. (1 + (Real.tan x_1))) ((1 : ℝ) /. (Real.tan x_1)))) (𝓝[≠] 0) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(Real.pi /. 4)) (Real.pi /. 4)))) ∧ (x ≠ 0)) → (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.tan ((Real.pi /. 4) - x_1)) ((1 : ℝ) /. (Real.tan x_1)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x_1 : ℝ => (Real.rpow ((1 - (Real.tan x_1)) /. (1 + (Real.tan x_1))) ((1 : ℝ) /. (Real.tan x_1)))))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow (1 + (1 /. ((1 + (Real.tan x)) /. ((-(2 : ℝ)) * (Real.tan x))))) ((-((1 + (Real.tan x)) /. (2 * (Real.tan x)))) * ((-(2 : ℝ)) /. (1 + (Real.tan x)))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (Real.rpow ((1 - (Real.tan x)) /. (1 + (Real.tan x))) ((1 : ℝ) /. (Real.tan x)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (Real.rpow (1 + (1 /. ((1 + (Real.tan x)) /. ((-(2 : ℝ)) * (Real.tan x))))) ((-((1 + (Real.tan x)) /. (2 * (Real.tan x)))) * ((-(2 : ℝ)) /. (1 + (Real.tan x)))))))))) := by
  sorry

theorem proof_gap_exercise_524_3
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow ((1 - (Real.tan x_1)) /. (1 + (Real.tan x_1))) ((1 : ℝ) /. (Real.tan x_1)))) (𝓝[≠] 0) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(Real.pi /. 4)) (Real.pi /. 4)))) ∧ (x ≠ 0)) → (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.tan ((Real.pi /. 4) - x_1)) ((1 : ℝ) /. (Real.tan x_1)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x_1 : ℝ => (Real.rpow ((1 - (Real.tan x_1)) /. (1 + (Real.tan x_1))) ((1 : ℝ) /. (Real.tan x_1)))))))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow ((1 - (Real.tan x)) /. (1 + (Real.tan x))) ((1 : ℝ) /. (Real.tan x)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (Real.rpow (1 + (1 /. ((1 + (Real.tan x)) /. ((-(2 : ℝ)) * (Real.tan x))))) ((-((1 + (Real.tan x)) /. (2 * (Real.tan x)))) * ((-(2 : ℝ)) /. (1 + (Real.tan x)))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow (1 + (1 /. ((1 + (Real.tan x)) /. ((-(2 : ℝ)) * (Real.tan x))))) ((-((1 + (Real.tan x)) /. (2 * (Real.tan x)))) * ((-(2 : ℝ)) /. (1 + (Real.tan x)))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow (1 + (1 /. ((1 + (Real.tan x)) /. ((-(2 : ℝ)) * (Real.tan x))))) ((-((1 + (Real.tan x)) /. (2 * (Real.tan x)))) * ((-(2 : ℝ)) /. (1 + (Real.tan x)))))) (𝓝[≠] 0) (𝓝 (Real.exp (-(2 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_524_4
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow ((1 - (Real.tan x_1)) /. (1 + (Real.tan x_1))) ((1 : ℝ) /. (Real.tan x_1)))) (𝓝[≠] 0) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo (-(Real.pi /. 4)) (Real.pi /. 4)))) ∧ (x ≠ 0)) → (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.tan ((Real.pi /. 4) - x_1)) ((1 : ℝ) /. (Real.tan x_1)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x_1 : ℝ => (Real.rpow ((1 - (Real.tan x_1)) /. (1 + (Real.tan x_1))) ((1 : ℝ) /. (Real.tan x_1)))))))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow ((1 - (Real.tan x)) /. (1 + (Real.tan x))) ((1 : ℝ) /. (Real.tan x)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (Real.rpow (1 + (1 /. ((1 + (Real.tan x)) /. ((-(2 : ℝ)) * (Real.tan x))))) ((-((1 + (Real.tan x)) /. (2 * (Real.tan x)))) * ((-(2 : ℝ)) /. (1 + (Real.tan x)))))))))
  (h3 : Tendsto (fun x : ℝ => (Real.rpow (1 + (1 /. ((1 + (Real.tan x)) /. ((-(2 : ℝ)) * (Real.tan x))))) ((-((1 + (Real.tan x)) /. (2 * (Real.tan x)))) * ((-(2 : ℝ)) /. (1 + (Real.tan x)))))) (𝓝[≠] 0) (𝓝 (Real.exp (-(2 : ℝ)))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow (1 + (1 /. ((1 + (Real.tan x)) /. ((-(2 : ℝ)) * (Real.tan x))))) ((-((1 + (Real.tan x)) /. (2 * (Real.tan x)))) * ((-(2 : ℝ)) /. (1 + (Real.tan x)))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow (Real.tan ((Real.pi /. 4) - x)) ((1 : ℝ) /. (Real.tan x)))) (𝓝[≠] 0) (𝓝 (Real.exp (-(2 : ℝ)))) := by
  sorry
