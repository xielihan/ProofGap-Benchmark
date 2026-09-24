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

-- exercise: exercise_1360

theorem proof_gap_exercise_1360_1
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.rpow (a + x) x) - (Real.rpow a x)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))))))) := by
  sorry

theorem proof_gap_exercise_1360_2
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow (a + x) x) - (Real.rpow a x)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * (((Real.log (a + x)) + (x /. (a + x))) ^ (2 : ℕ))) + ((Real.rpow (a + x) x) * ((1 /. (a + x)) + (a /. ((a + x) ^ (2 : ℕ)))))) - ((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))) (𝓝[≠] 0) (𝓝 ((1 /. 2) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * (((Real.log (a + x)) + (x /. (a + x))) ^ (2 : ℕ))) + ((Real.rpow (a + x) x) * ((1 /. (a + x)) + (a /. ((a + x) ^ (2 : ℕ)))))) - ((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_1360_3
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow (a + x) x) - (Real.rpow a x)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))))))
  (h4 : Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))) (𝓝[≠] 0) (𝓝 ((1 /. 2) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * (((Real.log (a + x)) + (x /. (a + x))) ^ (2 : ℕ))) + ((Real.rpow (a + x) x) * ((1 /. (a + x)) + (a /. ((a + x) ^ (2 : ℕ)))))) - ((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * (((Real.log (a + x)) + (x /. (a + x))) ^ (2 : ℕ))) + ((Real.rpow (a + x) x) * ((1 /. (a + x)) + (a /. ((a + x) ^ (2 : ℕ)))))) - ((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : ((1 /. 2) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * (((Real.log (a + x)) + (x /. (a + x))) ^ (2 : ℕ))) + ((Real.rpow (a + x) x) * ((1 /. (a + x)) + (a /. ((a + x) ^ (2 : ℕ)))))) - ((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ)))))) = (1 /. a) := by
  sorry

theorem proof_gap_exercise_1360_4
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : Tendsto (fun x : ℝ => (((Real.rpow (a + x) x) - (Real.rpow a x)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))))))
  (h4 : Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))) (𝓝[≠] 0) (𝓝 ((1 /. 2) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * (((Real.log (a + x)) + (x /. (a + x))) ^ (2 : ℕ))) + ((Real.rpow (a + x) x) * ((1 /. (a + x)) + (a /. ((a + x) ^ (2 : ℕ)))))) - ((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))))))))
  (h5 : ((1 /. 2) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.rpow (a + x) x) * (((Real.log (a + x)) + (x /. (a + x))) ^ (2 : ℕ))) + ((Real.rpow (a + x) x) * ((1 /. (a + x)) + (a /. ((a + x) ^ (2 : ℕ)))))) - ((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ)))))) = (1 /. a))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * ((Real.log (a + x)) + (x /. (a + x)))) - ((Real.rpow a x) * (Real.log a))) /. (2 * x))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.rpow (a + x) x) * (((Real.log (a + x)) + (x /. (a + x))) ^ (2 : ℕ))) + ((Real.rpow (a + x) x) * ((1 /. (a + x)) + (a /. ((a + x) ^ (2 : ℕ)))))) - ((Real.rpow a x) * ((Real.log a) ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.rpow (a + x) x) - (Real.rpow a x)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (1 /. a)) := by
  sorry
