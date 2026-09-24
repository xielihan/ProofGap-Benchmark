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

-- exercise: exercise_1329

theorem proof_gap_exercise_1329_1
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow a x) - (Real.rpow a (Real.sin x))) /. (x ^ (3 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_1329_2
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : Tendsto (fun x : ℝ => (((Real.rpow a x) - (Real.rpow a (Real.sin x))) /. (x ^ (3 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 (((Real.log a) /. 3) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x))))))) := by
  sorry

theorem proof_gap_exercise_1329_3
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : Tendsto (fun x : ℝ => (((Real.rpow a x) - (Real.rpow a (Real.sin x))) /. (x ^ (3 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 (((Real.log a) /. 3) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))) + ((Real.rpow a (Real.sin x)) * (Real.cos x))) + ((((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin x)) * (Real.cos x))) + (((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin (2 * x)))) - (((Real.rpow a (Real.sin x)) * ((Real.log a) ^ (2 : ℕ))) * ((Real.cos x) ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ ((((Real.log a) /. 3) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x)))) = (((Real.log a) /. 6) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))) + ((Real.rpow a (Real.sin x)) * (Real.cos x))) + ((((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin x)) * (Real.cos x))) + (((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin (2 * x)))) - (((Real.rpow a (Real.sin x)) * ((Real.log a) ^ (2 : ℕ))) * ((Real.cos x) ^ (3 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1329_4
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : Tendsto (fun x : ℝ => (((Real.rpow a x) - (Real.rpow a (Real.sin x))) /. (x ^ (3 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 (((Real.log a) /. 3) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x))))))
  (h4 : (((Real.log a) /. 3) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x)))) = (((Real.log a) /. 6) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))) + ((Real.rpow a (Real.sin x)) * (Real.cos x))) + ((((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin x)) * (Real.cos x))) + (((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin (2 * x)))) - (((Real.rpow a (Real.sin x)) * ((Real.log a) ^ (2 : ℕ))) * ((Real.cos x) ^ (3 : ℕ)))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))) + ((Real.rpow a (Real.sin x)) * (Real.cos x))) + ((((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin x)) * (Real.cos x))) + (((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin (2 * x)))) - (((Real.rpow a (Real.sin x)) * ((Real.log a) ^ (2 : ℕ))) * ((Real.cos x) ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : (((Real.log a) /. 6) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))) + ((Real.rpow a (Real.sin x)) * (Real.cos x))) + ((((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin x)) * (Real.cos x))) + (((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin (2 * x)))) - (((Real.rpow a (Real.sin x)) * ((Real.log a) ^ (2 : ℕ))) * ((Real.cos x) ^ (3 : ℕ)))))) = ((Real.log a) /. 6) := by
  sorry

theorem proof_gap_exercise_1329_5
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : Tendsto (fun x : ℝ => (((Real.rpow a x) - (Real.rpow a (Real.sin x))) /. (x ^ (3 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 (((Real.log a) /. 3) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x))))))
  (h4 : (((Real.log a) /. 3) * (𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x)))) = (((Real.log a) /. 6) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))) + ((Real.rpow a (Real.sin x)) * (Real.cos x))) + ((((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin x)) * (Real.cos x))) + (((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin (2 * x)))) - (((Real.rpow a (Real.sin x)) * ((Real.log a) ^ (2 : ℕ))) * ((Real.cos x) ^ (3 : ℕ)))))))
  (h5 : (((Real.log a) /. 6) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))) + ((Real.rpow a (Real.sin x)) * (Real.cos x))) + ((((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin x)) * (Real.cos x))) + (((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin (2 * x)))) - (((Real.rpow a (Real.sin x)) * ((Real.log a) ^ (2 : ℕ))) * ((Real.cos x) ^ (3 : ℕ)))))) = ((Real.log a) /. 6))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow a x) - ((Real.rpow a (Real.sin x)) * (Real.cos x))) * (Real.log a)) /. (3 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.rpow a x) * (Real.log a)) + ((Real.rpow a (Real.sin x)) * (Real.sin x))) - (((Real.rpow a (Real.sin x)) * (Real.log a)) * ((Real.cos x) ^ (2 : ℕ)))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))) + ((Real.rpow a (Real.sin x)) * (Real.cos x))) + ((((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin x)) * (Real.cos x))) + (((Real.rpow a (Real.sin x)) * (Real.log a)) * (Real.sin (2 * x)))) - (((Real.rpow a (Real.sin x)) * ((Real.log a) ^ (2 : ℕ))) * ((Real.cos x) ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.rpow a x) - (Real.rpow a (Real.sin x))) /. (x ^ (3 : ℕ)))) (𝓝[≠] 0) (𝓝 ((Real.log a) /. 6)) := by
  sorry
