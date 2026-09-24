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

-- exercise: exercise_489

theorem proof_gap_exercise_489_1
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) = (((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a)))))) := by
  sorry

theorem proof_gap_exercise_489_2
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) = (((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a)))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_489_3
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) = (((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a)))))))
  (h3 : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_489_4
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) = (((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a)))))))
  (h3 : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))))))
  (h4 : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((2 * (Real.sin (x /. 2))) * ((Real.sin (a + ((3 * x) /. 2))) - (Real.sin (a + (x /. 2))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(𝓝[≠] 0).limUnder (fun x : ℝ => (((2 * (Real.sin (x /. 2))) * ((Real.sin (a + ((3 * x) /. 2))) - (Real.sin (a + (x /. 2))))) /. (x ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_489_5
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) = (((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a)))))))
  (h3 : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))))))
  (h4 : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))))))
  (h5 : Tendsto (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(𝓝[≠] 0).limUnder (fun x : ℝ => (((2 * (Real.sin (x /. 2))) * ((Real.sin (a + ((3 * x) /. 2))) - (Real.sin (a + (x /. 2))))) /. (x ^ (2 : ℕ)))))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((2 * (Real.sin (x /. 2))) * ((Real.sin (a + ((3 * x) /. 2))) - (Real.sin (a + (x /. 2))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.sin (x /. 2)) /. (x /. 2)) ^ (2 : ℕ)) * (Real.cos (a + x)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.sin (x /. 2)) /. (x /. 2)) ^ (2 : ℕ)) * (Real.cos (a + x)))))))) := by
  sorry

theorem proof_gap_exercise_489_6
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) = (((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a)))))))
  (h3 : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))))))
  (h4 : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))))))
  (h5 : Tendsto (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(𝓝[≠] 0).limUnder (fun x : ℝ => (((2 * (Real.sin (x /. 2))) * ((Real.sin (a + ((3 * x) /. 2))) - (Real.sin (a + (x /. 2))))) /. (x ^ (2 : ℕ)))))))
  (h6 : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(𝓝[≠] 0).limUnder (fun x : ℝ => ((((Real.sin (x /. 2)) /. (x /. 2)) ^ (2 : ℕ)) * (Real.cos (a + x)))))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (Real.cos (a + x))) - ((Real.cos (a + x)) - (Real.cos a))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((-(2 : ℝ)) * (Real.sin (a + ((3 * x) /. 2)))) * (Real.sin (x /. 2))) + ((2 * (Real.sin (a + (x /. 2)))) * (Real.sin (x /. 2)))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((2 * (Real.sin (x /. 2))) * ((Real.sin (a + ((3 * x) /. 2))) - (Real.sin (a + (x /. 2))))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 L))
  (h10 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((Real.sin (x /. 2)) /. (x /. 2)) ^ (2 : ℕ)) * (Real.cos (a + x)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((((Real.cos (a + (2 * x))) - (2 * (Real.cos (a + x)))) + (Real.cos a)) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (-(Real.cos a))) := by
  sorry
