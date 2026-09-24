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

-- exercise: exercise_531

theorem proof_gap_exercise_531_1
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))) := by
  sorry

theorem proof_gap_exercise_531_2
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))))
  : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a))) := by
  sorry

theorem proof_gap_exercise_531_3
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((Real.log x) - (Real.log a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))))))) := by
  sorry

theorem proof_gap_exercise_531_4
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a))))
  (h5 : Tendsto (fun x : ℝ => (((Real.log x) - (Real.log a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))))))) := by
  sorry

theorem proof_gap_exercise_531_5
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a))))
  (h5 : Tendsto (fun x : ℝ => (((Real.log x) - (Real.log a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))))))
  (h6 : Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))))))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 (Real.log (Real.exp (1 /. a)))) := by
  sorry

theorem proof_gap_exercise_531_6
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a))))
  (h5 : Tendsto (fun x : ℝ => (((Real.log x) - (Real.log a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))))))
  (h6 : Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))))))
  (h7 : Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 (Real.log (Real.exp (1 /. a)))))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 L))
  : (Real.log (Real.exp (1 /. a))) = (1 /. a) := by
  sorry

theorem proof_gap_exercise_531_7
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a))))
  (h5 : Tendsto (fun x : ℝ => (((Real.log x) - (Real.log a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))))))
  (h6 : Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))))))
  (h7 : Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 (Real.log (Real.exp (1 /. a)))))
  (h8 : (Real.log (Real.exp (1 /. a))) = (1 /. a))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 L))
  (h10 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 (1 /. a)) := by
  sorry

theorem proof_gap_exercise_531_8
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))))
  (h4 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ a))))
  (h5 : Tendsto (fun x : ℝ => (((Real.log x) - (Real.log a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))))))
  (h6 : Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((𝓝[≠] a).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))))))
  (h7 : Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 (Real.log (Real.exp (1 /. a)))))
  (h8 : (Real.log (Real.exp (1 /. a))) = (1 /. a))
  (h9 : Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 (1 /. a)))
  (h10 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((Real.log (x /. a)) /. (x - a))) (𝓝[≠] a) (𝓝 L))
  (h11 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + (1 /. (a /. (x - a)))) ((a /. (x - a)) * (1 /. a))))) (𝓝[≠] a) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.log x) - (Real.log a)) /. (x - a))) (𝓝[≠] a) (𝓝 (1 /. a)) := by
  sorry
