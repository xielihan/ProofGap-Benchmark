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

-- exercise: exercise_504

theorem proof_gap_exercise_504_1
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((1 - (((Real.cos x) * (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_504_2
  (h1 : Tendsto (fun x : ℝ => ((1 - (((Real.cos x) * (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))))))
  (h2 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) + ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (1 - (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((1 /. 2) + (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) + ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (1 - (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))))) /. (x ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_504_3
  (h1 : Tendsto (fun x : ℝ => ((1 - (((Real.cos x) * (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))))))
  (h2 : Tendsto (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((1 /. 2) + (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) + ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (1 - (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))))) /. (x ^ (2 : ℕ)))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) + ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (1 - (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((1 - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (1 + (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L) ∧ ∃ L : ℝ, Tendsto (fun x : ℝ => ((1 - (Real.cos (3 * x))) /. ((x ^ (2 : ℕ)) * ((1 + (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))) + (Real.rpow ((Real.cos (3 * x)) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L) ∧ (((1 /. 2) + (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) + ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (1 - (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))))) /. (x ^ (2 : ℕ))))) = (((1 /. 2) + (𝓝[≠] 0).limUnder (fun x : ℝ => ((1 - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (1 + (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))))))) + (𝓝[≠] 0).limUnder (fun x : ℝ => ((1 - (Real.cos (3 * x))) /. ((x ^ (2 : ℕ)) * ((1 + (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))) + (Real.rpow ((Real.cos (3 * x)) ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))) := by
  sorry

theorem proof_gap_exercise_504_4
  (h1 : Tendsto (fun x : ℝ => ((1 - (((Real.cos x) * (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))))))
  (h2 : Tendsto (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((1 /. 2) + (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) + ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (1 - (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))))) /. (x ^ (2 : ℕ)))))))
  (h3 : ((1 /. 2) + (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 - (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) + ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (1 - (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))))) /. (x ^ (2 : ℕ))))) = (((1 /. 2) + (𝓝[≠] 0).limUnder (fun x : ℝ => ((1 - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (1 + (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))))))) + (𝓝[≠] 0).limUnder (fun x : ℝ => ((1 - (Real.cos (3 * x))) /. ((x ^ (2 : ℕ)) * ((1 + (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))) + (Real.rpow ((Real.cos (3 * x)) ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.cos x)) + ((Real.cos x) * (1 - ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 - (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) + ((Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)) * (1 - (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((1 - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (1 + (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((1 - (Real.cos (3 * x))) /. ((x ^ (2 : ℕ)) * ((1 + (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹))) + (Real.rpow ((Real.cos (3 * x)) ^ (2 : ℕ)) (((3 : ℝ))⁻¹)))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((1 - (((Real.cos x) * (Real.rpow (Real.cos (2 * x)) (((2 : ℝ))⁻¹))) * (Real.rpow (Real.cos (3 * x)) (((3 : ℝ))⁻¹)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 3) := by
  sorry
