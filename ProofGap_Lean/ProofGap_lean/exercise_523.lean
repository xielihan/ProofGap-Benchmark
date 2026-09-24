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

-- exercise: exercise_523

theorem proof_gap_exercise_523_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 Real.pi))) ∧ (x ≠ (Real.pi /. 2))) → (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.sin x_1) (Real.tan x_1))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))))))))) := by
  sorry

theorem proof_gap_exercise_523_2
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 Real.pi))) ∧ (x ≠ (Real.pi /. 2))) → (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.sin x_1) (Real.tan x_1))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) (-((Real.tan x) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))))))) := by
  sorry

theorem proof_gap_exercise_523_3
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 Real.pi))) ∧ (x ≠ (Real.pi /. 2))) → (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.sin x_1) (Real.tan x_1))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))))))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) (-((Real.tan x) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 (Real.exp (0 : ℝ))) := by
  sorry

theorem proof_gap_exercise_523_4
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 Real.pi))) ∧ (x ≠ (Real.pi /. 2))) → (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.sin x_1) (Real.tan x_1))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))))))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) (-((Real.tan x) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))))))
  (h3 : Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 (Real.exp (0 : ℝ))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L))
  : (Real.exp (0 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_523_5
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ioo 0 Real.pi))) ∧ (x ≠ (Real.pi /. 2))) → (Tendsto (fun x_1 : ℝ => (Real.rpow (Real.sin x_1) (Real.tan x_1))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x_1 : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x_1)) ^ (2 : ℕ))) (-((Real.tan x_1) /. 2)))))))))))
  (h2 : Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) (-((Real.tan x) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 ((𝓝[≠] (Real.pi /. 2)).limUnder (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))))))
  (h3 : Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 (Real.exp (0 : ℝ))))
  (h4 : (Real.exp (0 : ℝ)) = 1)
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow (1 + (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) ((1 /. (((1 : ℝ) /. (Real.tan x)) ^ (2 : ℕ))) * ((-((1 : ℝ) /. (Real.tan x))) /. 2)))) (𝓝[≠] (Real.pi /. 2)) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.rpow (Real.sin x) (Real.tan x))) (𝓝[≠] (Real.pi /. 2)) (𝓝 1) := by
  sorry
