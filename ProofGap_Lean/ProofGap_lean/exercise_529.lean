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

-- exercise: exercise_529

theorem proof_gap_exercise_529_1
  : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > (-(1 : ℝ))))) := by
  sorry

theorem proof_gap_exercise_529_2
  (h1 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > (-(1 : ℝ))))))
  : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))) := by
  sorry

theorem proof_gap_exercise_529_3
  (h1 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > (-(1 : ℝ))))))
  (h2 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))))))) := by
  sorry

theorem proof_gap_exercise_529_4
  (h1 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > (-(1 : ℝ))))))
  (h2 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 (Real.log (Real.exp 1))) := by
  sorry

theorem proof_gap_exercise_529_5
  (h1 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > (-(1 : ℝ))))))
  (h2 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))))))
  (h4 : Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 (Real.log (Real.exp 1))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : (Real.log (Real.exp 1)) = 1 := by
  sorry

theorem proof_gap_exercise_529_6
  (h1 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > (-(1 : ℝ))))))
  (h2 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))))))
  (h4 : Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 (Real.log (Real.exp 1))))
  (h5 : (Real.log (Real.exp 1)) = 1)
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[≠] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_529_7
  (h1 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x > (-(1 : ℝ))))))
  (h2 : (exists (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))))))
  (h4 : Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 (Real.log (Real.exp 1))))
  (h5 : (Real.log (Real.exp 1)) = 1)
  (h6 : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[≠] 0) (𝓝 1))
  (h7 : ∃ L : ℝ, Tendsto (fun x : ℝ => (Real.log (Real.rpow (1 + x) (1 /. x)))) (𝓝[≠] 0) (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.log (1 + x)) /. x)) (𝓝[≠] 0) (𝓝 1) := by
  sorry
