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

-- exercise: exercise_418

theorem proof_gap_exercise_418_1
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 3)) ∧ (x ≠ 5)) → ((((((x ^ (2 : ℕ)) - (5 * x)) + 6) /. (((x ^ (2 : ℕ)) - (8 * x)) + 15)) = (((x - 3) * (x - 2)) /. ((x - 3) * (x - 5)))) ∧ ((((x - 3) * (x - 2)) /. ((x - 3) * (x - 5))) = ((x - 2) /. (x - 5)))))) := by
  sorry

theorem proof_gap_exercise_418_2
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 3)) ∧ (x ≠ 5)) → ((((((x ^ (2 : ℕ)) - (5 * x)) + 6) /. (((x ^ (2 : ℕ)) - (8 * x)) + 15)) = (((x - 3) * (x - 2)) /. ((x - 3) * (x - 5)))) ∧ ((((x - 3) * (x - 2)) /. ((x - 3) * (x - 5))) = ((x - 2) /. (x - 5)))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((x - 2) /. (x - 5))) (𝓝[≠] 3) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((x ^ (2 : ℕ)) - (5 * x)) + 6) /. (((x ^ (2 : ℕ)) - (8 * x)) + 15))) (𝓝[≠] 3) (𝓝 ((𝓝[≠] 3).limUnder (fun x : ℝ => ((x - 2) /. (x - 5))))))) := by
  sorry

theorem proof_gap_exercise_418_3
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 3)) ∧ (x ≠ 5)) → ((((((x ^ (2 : ℕ)) - (5 * x)) + 6) /. (((x ^ (2 : ℕ)) - (8 * x)) + 15)) = (((x - 3) * (x - 2)) /. ((x - 3) * (x - 5)))) ∧ ((((x - 3) * (x - 2)) /. ((x - 3) * (x - 5))) = ((x - 2) /. (x - 5)))))))
  (h2 : Tendsto (fun x : ℝ => ((((x ^ (2 : ℕ)) - (5 * x)) + 6) /. (((x ^ (2 : ℕ)) - (8 * x)) + 15))) (𝓝[≠] 3) (𝓝 ((𝓝[≠] 3).limUnder (fun x : ℝ => ((x - 2) /. (x - 5))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x - 2) /. (x - 5))) (𝓝[≠] 3) (𝓝 L))
  : Tendsto (fun x : ℝ => ((x - 2) /. (x - 5))) (𝓝[≠] 3) (𝓝 (-(1 /. 2))) := by
  sorry

theorem proof_gap_exercise_418_4
  (h1 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 3)) ∧ (x ≠ 5)) → ((((((x ^ (2 : ℕ)) - (5 * x)) + 6) /. (((x ^ (2 : ℕ)) - (8 * x)) + 15)) = (((x - 3) * (x - 2)) /. ((x - 3) * (x - 5)))) ∧ ((((x - 3) * (x - 2)) /. ((x - 3) * (x - 5))) = ((x - 2) /. (x - 5)))))))
  (h2 : Tendsto (fun x : ℝ => ((((x ^ (2 : ℕ)) - (5 * x)) + 6) /. (((x ^ (2 : ℕ)) - (8 * x)) + 15))) (𝓝[≠] 3) (𝓝 ((𝓝[≠] 3).limUnder (fun x : ℝ => ((x - 2) /. (x - 5))))))
  (h3 : Tendsto (fun x : ℝ => ((x - 2) /. (x - 5))) (𝓝[≠] 3) (𝓝 (-(1 /. 2))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x - 2) /. (x - 5))) (𝓝[≠] 3) (𝓝 L))
  : Tendsto (fun x : ℝ => ((((x ^ (2 : ℕ)) - (5 * x)) + 6) /. (((x ^ (2 : ℕ)) - (8 * x)) + 15))) (𝓝[≠] 3) (𝓝 (-(1 /. 2))) := by
  sorry
