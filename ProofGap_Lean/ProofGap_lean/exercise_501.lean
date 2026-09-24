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

-- exercise: exercise_501

theorem proof_gap_exercise_501_1
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow (Real.cos x) (((2 : ℝ))⁻¹)) - (Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_501_2
  (h1 : Tendsto (fun x : ℝ => (((Real.rpow (Real.cos x) (((2 : ℝ))⁻¹)) - (Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))))))
  (h2 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.cos x)) /. ((Real.sin x) ^ (2 : ℕ))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) /. ((Real.sin x) ^ (2 : ℕ))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹)))))))))) := by
  sorry

theorem proof_gap_exercise_501_3
  (h1 : Tendsto (fun x : ℝ => (((Real.rpow (Real.cos x) (((2 : ℝ))⁻¹)) - (Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))))))
  (h2 : Tendsto (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) /. ((Real.sin x) ^ (2 : ℕ))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹)))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.cos x)) /. ((Real.sin x) ^ (2 : ℕ))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((2 * ((Real.sin (x /. 2)) ^ (2 : ℕ))) /. (4 * ((x /. 2) ^ (2 : ℕ)))) * ((x ^ (2 : ℕ)) /. ((Real.sin x) ^ (2 : ℕ)))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L) ∧ ((-(𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) /. ((Real.sin x) ^ (2 : ℕ))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹))))))) = (-(𝓝[≠] 0).limUnder (fun x : ℝ => ((((2 * ((Real.sin (x /. 2)) ^ (2 : ℕ))) /. (4 * ((x /. 2) ^ (2 : ℕ)))) * ((x ^ (2 : ℕ)) /. ((Real.sin x) ^ (2 : ℕ)))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹))))))))) := by
  sorry

theorem proof_gap_exercise_501_4
  (h1 : Tendsto (fun x : ℝ => (((Real.rpow (Real.cos x) (((2 : ℝ))⁻¹)) - (Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))))))
  (h2 : Tendsto (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) /. ((Real.sin x) ^ (2 : ℕ))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹)))))))))
  (h3 : (-(𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) /. ((Real.sin x) ^ (2 : ℕ))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹))))))) = (-(𝓝[≠] 0).limUnder (fun x : ℝ => ((((2 * ((Real.sin (x /. 2)) ^ (2 : ℕ))) /. (4 * ((x /. 2) ^ (2 : ℕ)))) * ((x ^ (2 : ℕ)) /. ((Real.sin x) ^ (2 : ℕ)))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((-(Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) * (1 - (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹)))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.cos x)) /. ((Real.sin x) ^ (2 : ℕ))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((2 * ((Real.sin (x /. 2)) ^ (2 : ℕ))) /. (4 * ((x /. 2) ^ (2 : ℕ)))) * ((x ^ (2 : ℕ)) /. ((Real.sin x) ^ (2 : ℕ)))) * ((Real.rpow (Real.cos x) (((3 : ℝ))⁻¹)) /. (((((1 + (Real.rpow (Real.cos x) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (2 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (3 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (4 : ℕ)) (((6 : ℝ))⁻¹))) + (Real.rpow ((Real.cos x) ^ (5 : ℕ)) (((6 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.rpow (Real.cos x) (((2 : ℝ))⁻¹)) - (Real.rpow (Real.cos x) (((3 : ℝ))⁻¹))) /. ((Real.sin x) ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(1 /. 12))) := by
  sorry
