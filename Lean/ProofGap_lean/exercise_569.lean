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

-- exercise: exercise_569

theorem proof_gap_exercise_569_1
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 1))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (0 < x))
  (h3 : x < (1 /. a))
  : (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))))))) := by
  sorry

theorem proof_gap_exercise_569_2
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 1))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (0 < x))
  (h3 : x < (1 /. a))
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))) (𝓝[>] 0) (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (1 + ((2 * (Real.log a)) /. ((Real.log x_1) - (Real.log a)))) ((((((Real.log x_1) - (Real.log a)) /. (2 * (Real.log a))) * 2) * (Real.log a)) * (((Real.log x_1) + (Real.log (Real.log a))) /. ((Real.log x_1) - (Real.log a))))))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (1 + ((2 * (Real.log a)) /. ((Real.log x_1) - (Real.log a)))) ((((((Real.log x_1) - (Real.log a)) /. (2 * (Real.log a))) * 2) * (Real.log a)) * (((Real.log x_1) + (Real.log (Real.log a))) /. ((Real.log x_1) - (Real.log a))))))))))) := by
  sorry

theorem proof_gap_exercise_569_3
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 1))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (0 < x))
  (h3 : x < (1 /. a))
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))))))
  (h5 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (1 + ((2 * (Real.log a)) /. ((Real.log x_1) - (Real.log a)))) ((((((Real.log x_1) - (Real.log a)) /. (2 * (Real.log a))) * 2) * (Real.log a)) * (((Real.log x_1) + (Real.log (Real.log a))) /. ((Real.log x_1) - (Real.log a))))))))))
  (h6 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))) (𝓝[>] 0) (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (1 + ((2 * (Real.log a)) /. ((Real.log x_1) - (Real.log a)))) ((((((Real.log x_1) - (Real.log a)) /. (2 * (Real.log a))) * 2) * (Real.log a)) * (((Real.log x_1) + (Real.log (Real.log a))) /. ((Real.log x_1) - (Real.log a))))))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 (Real.log (Real.exp (Real.log (a ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_569_4
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 1))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (0 < x))
  (h3 : x < (1 /. a))
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))))))
  (h5 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (1 + ((2 * (Real.log a)) /. ((Real.log x_1) - (Real.log a)))) ((((((Real.log x_1) - (Real.log a)) /. (2 * (Real.log a))) * 2) * (Real.log a)) * (((Real.log x_1) + (Real.log (Real.log a))) /. ((Real.log x_1) - (Real.log a))))))))))
  (h6 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 (Real.log (Real.exp (Real.log (a ^ (2 : ℕ)))))))
  (h7 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))) (𝓝[>] 0) (𝓝 L))
  (h8 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (1 + ((2 * (Real.log a)) /. ((Real.log x_1) - (Real.log a)))) ((((((Real.log x_1) - (Real.log a)) /. (2 * (Real.log a))) * 2) * (Real.log a)) * (((Real.log x_1) + (Real.log (Real.log a))) /. ((Real.log x_1) - (Real.log a))))))) (𝓝[>] 0) (𝓝 L))
  : (Real.log (Real.exp (Real.log (a ^ (2 : ℕ))))) = (Real.log (a ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_569_5
  (a : ℝ)
  (x : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 1))
  (h2 : (x ∈ (Set.univ : Set ℝ)) ∧ (0 < x))
  (h3 : x < (1 /. a))
  (h4 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))))))
  (h5 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x_1 : ℝ => (Real.log (Real.rpow (1 + ((2 * (Real.log a)) /. ((Real.log x_1) - (Real.log a)))) ((((((Real.log x_1) - (Real.log a)) /. (2 * (Real.log a))) * 2) * (Real.log a)) * (((Real.log x_1) + (Real.log (Real.log a))) /. ((Real.log x_1) - (Real.log a))))))))))
  (h6 : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 (Real.log (Real.exp (Real.log (a ^ (2 : ℕ)))))))
  (h7 : (Real.log (Real.exp (Real.log (a ^ (2 : ℕ))))) = (Real.log (a ^ (2 : ℕ))))
  (h8 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (((Real.log a) + (Real.log x_1)) /. ((Real.log x_1) - (Real.log a))) ((Real.log x_1) + (Real.log (Real.log a)))))) (𝓝[>] 0) (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun x_1 : ℝ => (Real.log (Real.rpow (1 + ((2 * (Real.log a)) /. ((Real.log x_1) - (Real.log a)))) ((((((Real.log x_1) - (Real.log a)) /. (2 * (Real.log a))) * 2) * (Real.log a)) * (((Real.log x_1) + (Real.log (Real.log a))) /. ((Real.log x_1) - (Real.log a))))))) (𝓝[>] 0) (𝓝 L))
  : Tendsto (fun x_1 : ℝ => ((Real.log (x_1 * (Real.log a))) * (Real.log ((Real.log (a * x_1)) /. (Real.log (x_1 /. a)))))) (𝓝[>] 0) (𝓝 (Real.log (a ^ (2 : ℕ)))) := by
  sorry
