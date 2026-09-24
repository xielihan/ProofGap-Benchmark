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

-- exercise: exercise_1333

theorem proof_gap_exercise_1333_1
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.cos (Real.sin x)) - (Real.cos x)) /. (x ^ (4 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_1333_2
  (h1 : Tendsto (fun x : ℝ => (((Real.cos (Real.sin x)) - (Real.cos x)) /. (x ^ (4 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))))))
  (h2 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))))))) := by
  sorry

theorem proof_gap_exercise_1333_3
  (h1 : Tendsto (fun x : ℝ => (((Real.cos (Real.sin x)) - (Real.cos x)) /. (x ^ (4 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))))))
  (h2 : Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))))))) := by
  sorry

theorem proof_gap_exercise_1333_4
  (h1 : Tendsto (fun x : ℝ => (((Real.cos (Real.sin x)) - (Real.cos x)) /. (x ^ (4 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))))))
  (h2 : Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))) (𝓝[≠] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((((((((-(Real.sin x)) * (Real.sin (Real.sin x))) + (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + ((3 * (Real.cos (2 * x))) * (Real.cos (Real.sin x)))) - ((((3 /. 2) * (Real.cos x)) * (Real.sin (2 * x))) * (Real.sin (Real.sin x)))) - (((3 * ((Real.cos x) ^ (2 : ℕ))) * (Real.sin x)) * (Real.sin (Real.sin x)))) + (((Real.cos x) ^ (4 : ℕ)) * (Real.cos (Real.sin x)))) - (Real.cos x))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))) (𝓝[≠] 0) (𝓝 ((1 /. 24) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((((-(Real.sin x)) * (Real.sin (Real.sin x))) + (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + ((3 * (Real.cos (2 * x))) * (Real.cos (Real.sin x)))) - ((((3 /. 2) * (Real.cos x)) * (Real.sin (2 * x))) * (Real.sin (Real.sin x)))) - (((3 * ((Real.cos x) ^ (2 : ℕ))) * (Real.sin x)) * (Real.sin (Real.sin x)))) + (((Real.cos x) ^ (4 : ℕ)) * (Real.cos (Real.sin x)))) - (Real.cos x))))))) := by
  sorry

theorem proof_gap_exercise_1333_5
  (h1 : Tendsto (fun x : ℝ => (((Real.cos (Real.sin x)) - (Real.cos x)) /. (x ^ (4 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))))))
  (h2 : Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))))))
  (h4 : Tendsto (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))) (𝓝[≠] 0) (𝓝 ((1 /. 24) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((((-(Real.sin x)) * (Real.sin (Real.sin x))) + (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + ((3 * (Real.cos (2 * x))) * (Real.cos (Real.sin x)))) - ((((3 /. 2) * (Real.cos x)) * (Real.sin (2 * x))) * (Real.sin (Real.sin x)))) - (((3 * ((Real.cos x) ^ (2 : ℕ))) * (Real.sin x)) * (Real.sin (Real.sin x)))) + (((Real.cos x) ^ (4 : ℕ)) * (Real.cos (Real.sin x)))) - (Real.cos x))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((((((-(Real.sin x)) * (Real.sin (Real.sin x))) + (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + ((3 * (Real.cos (2 * x))) * (Real.cos (Real.sin x)))) - ((((3 /. 2) * (Real.cos x)) * (Real.sin (2 * x))) * (Real.sin (Real.sin x)))) - (((3 * ((Real.cos x) ^ (2 : ℕ))) * (Real.sin x)) * (Real.sin (Real.sin x)))) + (((Real.cos x) ^ (4 : ℕ)) * (Real.cos (Real.sin x)))) - (Real.cos x))) (𝓝[≠] 0) (𝓝 L))
  : ((1 /. 24) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((((-(Real.sin x)) * (Real.sin (Real.sin x))) + (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + ((3 * (Real.cos (2 * x))) * (Real.cos (Real.sin x)))) - ((((3 /. 2) * (Real.cos x)) * (Real.sin (2 * x))) * (Real.sin (Real.sin x)))) - (((3 * ((Real.cos x) ^ (2 : ℕ))) * (Real.sin x)) * (Real.sin (Real.sin x)))) + (((Real.cos x) ^ (4 : ℕ)) * (Real.cos (Real.sin x)))) - (Real.cos x)))) = (1 /. 6) := by
  sorry

theorem proof_gap_exercise_1333_6
  (h1 : Tendsto (fun x : ℝ => (((Real.cos (Real.sin x)) - (Real.cos x)) /. (x ^ (4 : ℕ)))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))))))
  (h2 : Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))))))
  (h4 : Tendsto (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))) (𝓝[≠] 0) (𝓝 ((1 /. 24) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((((-(Real.sin x)) * (Real.sin (Real.sin x))) + (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + ((3 * (Real.cos (2 * x))) * (Real.cos (Real.sin x)))) - ((((3 /. 2) * (Real.cos x)) * (Real.sin (2 * x))) * (Real.sin (Real.sin x)))) - (((3 * ((Real.cos x) ^ (2 : ℕ))) * (Real.sin x)) * (Real.sin (Real.sin x)))) + (((Real.cos x) ^ (4 : ℕ)) * (Real.cos (Real.sin x)))) - (Real.cos x))))))
  (h5 : ((1 /. 24) * (𝓝[≠] 0).limUnder (fun x : ℝ => ((((((((-(Real.sin x)) * (Real.sin (Real.sin x))) + (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + ((3 * (Real.cos (2 * x))) * (Real.cos (Real.sin x)))) - ((((3 /. 2) * (Real.cos x)) * (Real.sin (2 * x))) * (Real.sin (Real.sin x)))) - (((3 * ((Real.cos x) ^ (2 : ℕ))) * (Real.sin x)) * (Real.sin (Real.sin x)))) + (((Real.cos x) ^ (4 : ℕ)) * (Real.cos (Real.sin x)))) - (Real.cos x)))) = (1 /. 6))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((-(Real.cos x)) * (Real.sin (Real.sin x))) + (Real.sin x)) /. (4 * (x ^ (3 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((Real.sin x) * (Real.sin (Real.sin x))) - (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + (Real.cos x)) /. (12 * (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((((((Real.cos x) * (Real.sin (Real.sin x))) + (((1 /. 2) * (Real.sin (2 * x))) * (Real.cos (Real.sin x)))) + ((Real.sin (2 * x)) * (Real.cos (Real.sin x)))) + (((Real.cos x) ^ (3 : ℕ)) * (Real.sin (Real.sin x)))) - (Real.sin x)) /. (24 * x))) (𝓝[≠] 0) (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((((((((-(Real.sin x)) * (Real.sin (Real.sin x))) + (((Real.cos x) ^ (2 : ℕ)) * (Real.cos (Real.sin x)))) + ((3 * (Real.cos (2 * x))) * (Real.cos (Real.sin x)))) - ((((3 /. 2) * (Real.cos x)) * (Real.sin (2 * x))) * (Real.sin (Real.sin x)))) - (((3 * ((Real.cos x) ^ (2 : ℕ))) * (Real.sin x)) * (Real.sin (Real.sin x)))) + (((Real.cos x) ^ (4 : ℕ)) * (Real.cos (Real.sin x)))) - (Real.cos x))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.cos (Real.sin x)) - (Real.cos x)) /. (x ^ (4 : ℕ)))) (𝓝[≠] 0) (𝓝 (1 /. 6)) := by
  sorry
