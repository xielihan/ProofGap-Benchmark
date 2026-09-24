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

-- exercise: exercise_477

theorem proof_gap_exercise_477_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  : (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => (((Real.cos x_1) - (Real.cos (3 * x_1))) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_477_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : Tendsto (fun x_1 : ℝ => (((Real.cos x_1) - (Real.cos (3 * x_1))) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((((Real.sin x_1) /. x_1) ^ (2 : ℕ)) * (Real.cos x_1))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (4 * (𝓝[≠] 0).limUnder (fun x_1 : ℝ => ((((Real.sin x_1) /. x_1) ^ (2 : ℕ)) * (Real.cos x_1))))))) := by
  sorry

theorem proof_gap_exercise_477_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : Tendsto (fun x_1 : ℝ => (((Real.cos x_1) - (Real.cos (3 * x_1))) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))))))
  (h4 : Tendsto (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (4 * (𝓝[≠] 0).limUnder (fun x_1 : ℝ => ((((Real.sin x_1) /. x_1) ^ (2 : ℕ)) * (Real.cos x_1))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((((Real.sin x_1) /. x_1) ^ (2 : ℕ)) * (Real.cos x_1))) (𝓝[≠] 0) (𝓝 L))
  : (4 * (𝓝[≠] 0).limUnder (fun x_1 : ℝ => ((((Real.sin x_1) /. x_1) ^ (2 : ℕ)) * (Real.cos x_1)))) = 4 := by
  sorry

theorem proof_gap_exercise_477_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : x ≠ 0)
  (h3 : Tendsto (fun x_1 : ℝ => (((Real.cos x_1) - (Real.cos (3 * x_1))) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))))))
  (h4 : Tendsto (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (4 * (𝓝[≠] 0).limUnder (fun x_1 : ℝ => ((((Real.sin x_1) /. x_1) ^ (2 : ℕ)) * (Real.cos x_1))))))
  (h5 : (4 * (𝓝[≠] 0).limUnder (fun x_1 : ℝ => ((((Real.sin x_1) /. x_1) ^ (2 : ℕ)) * (Real.cos x_1)))) = 4)
  (h6 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (((2 * (Real.sin (2 * x_1))) * (Real.sin x_1)) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((((Real.sin x_1) /. x_1) ^ (2 : ℕ)) * (Real.cos x_1))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x_1 : ℝ => (((Real.cos x_1) - (Real.cos (3 * x_1))) /. (x_1 ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 4) := by
  sorry
