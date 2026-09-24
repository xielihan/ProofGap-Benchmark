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

-- exercise: exercise_1359

theorem proof_gap_exercise_1359_1
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow (1 + x) (1 /. x)) - (Real.exp 1)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))))))) := by
  sorry

theorem proof_gap_exercise_1359_2
  (h1 : Tendsto (fun x : ℝ => (((Real.rpow (1 + x) (1 /. x)) - (Real.exp 1)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))))))
  (h2 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1359_3
  (h1 : Tendsto (fun x : ℝ => (((Real.rpow (1 + x) (1 /. x)) - (Real.exp 1)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 L))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L) ∧ (((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ))))) = ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x)))))) := by
  sorry

theorem proof_gap_exercise_1359_4
  (h1 : Tendsto (fun x : ℝ => (((Real.rpow (1 + x) (1 /. x)) - (Real.exp 1)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))))))
  (h3 : ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ))))) = ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x)))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. (2 * ((1 + x) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x)))) = ((-(Real.exp 1)) * (𝓝[≠] 0).limUnder (fun x : ℝ => (1 /. (2 * ((1 + x) ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1359_5
  (h1 : Tendsto (fun x : ℝ => (((Real.rpow (1 + x) (1 /. x)) - (Real.exp 1)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))))))
  (h3 : ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ))))) = ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x)))))
  (h4 : ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x)))) = ((-(Real.exp 1)) * (𝓝[≠] 0).limUnder (fun x : ℝ => (1 /. (2 * ((1 + x) ^ (2 : ℕ)))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. (2 * ((1 + x) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : ((-(Real.exp 1)) * (𝓝[≠] 0).limUnder (fun x : ℝ => (1 /. (2 * ((1 + x) ^ (2 : ℕ)))))) = (-((Real.exp 1) /. 2)) := by
  sorry

theorem proof_gap_exercise_1359_6
  (h1 : Tendsto (fun x : ℝ => (((Real.rpow (1 + x) (1 /. x)) - (Real.exp 1)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))))))
  (h2 : Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))))))
  (h3 : ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ))))) = ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x)))))
  (h4 : ((Real.exp 1) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x)))) = ((-(Real.exp 1)) * (𝓝[≠] 0).limUnder (fun x : ℝ => (1 /. (2 * ((1 + x) ^ (2 : ℕ)))))))
  (h5 : ((-(Real.exp 1)) * (𝓝[≠] 0).limUnder (fun x : ℝ => (1 /. (2 * ((1 + x) ^ (2 : ℕ)))))) = (-((Real.exp 1) /. 2)))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.rpow (1 + x) (1 /. x)) * ((1 /. (x * (1 + x))) - ((Real.log (1 + x)) /. (x ^ (2 : ℕ)))))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x /. (1 + x)) - (Real.log (1 + x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((1 /. ((1 + x) ^ (2 : ℕ))) - (1 /. (1 + x))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => (1 /. (2 * ((1 + x) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.rpow (1 + x) (1 /. x)) - (Real.exp 1)) /. x)) (𝓝[≠] 0) (𝓝 (-((Real.exp 1) /. 2))) := by
  sorry
