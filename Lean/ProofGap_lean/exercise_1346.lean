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

-- exercise: exercise_1346

theorem proof_gap_exercise_1346_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ 1)) → (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((1 /. x_1) /. (-(1 : ℝ)))) (𝓝[≠] 1) (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 - x_1))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x_1 : ℝ => ((1 /. x_1) /. (-(1 : ℝ)))))))))) := by
  sorry

theorem proof_gap_exercise_1346_2
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((1 /. x_1) /. (-(1 : ℝ)))) (𝓝[≠] 1) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ 1)) → (Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 - x_1))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x_1 : ℝ => ((1 /. x_1) /. (-(1 : ℝ)))))))))))
  : Tendsto (fun x : ℝ => ((1 /. x) /. (-(1 : ℝ)))) (𝓝[≠] 1) (𝓝 (-(1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1346_3
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((1 /. x_1) /. (-(1 : ℝ)))) (𝓝[≠] 1) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ 1)) → (Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 - x_1))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x_1 : ℝ => ((1 /. x_1) /. (-(1 : ℝ)))))))))))
  (h2 : Tendsto (fun x : ℝ => ((1 /. x) /. (-(1 : ℝ)))) (𝓝[≠] 1) (𝓝 (-(1 : ℝ))))
  : Tendsto (fun x : ℝ => ((Real.log x) /. (1 - x))) (𝓝[≠] 1) (𝓝 (-(1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1346_4
  (h1 : (forall (x : ℝ), (∃ L : ℝ, Tendsto (fun x_1 : ℝ => ((1 /. x_1) /. (-(1 : ℝ)))) (𝓝[≠] 1) (𝓝 L) ∧ ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ 1)) → (Tendsto (fun x_1 : ℝ => ((Real.log x_1) /. (1 - x_1))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x_1 : ℝ => ((1 /. x_1) /. (-(1 : ℝ)))))))))))
  (h2 : Tendsto (fun x : ℝ => ((1 /. x) /. (-(1 : ℝ)))) (𝓝[≠] 1) (𝓝 (-(1 : ℝ))))
  (h3 : Tendsto (fun x : ℝ => ((Real.log x) /. (1 - x))) (𝓝[≠] 1) (𝓝 (-(1 : ℝ))))
  : Tendsto (fun x : ℝ => (Real.rpow x (1 /. (1 - x)))) (𝓝[≠] 1) (𝓝 (Real.exp (-(1 : ℝ)))) := by
  sorry
