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

-- exercise: exercise_419

theorem proof_gap_exercise_419_1
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3)) = ((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3)))) ∧ (((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3))) = ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3)))))) := by
  sorry

theorem proof_gap_exercise_419_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3)) = ((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3)))) ∧ (((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3))) = ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3)))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))) (𝓝[≠] 1) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))))))) := by
  sorry

theorem proof_gap_exercise_419_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3)) = ((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3)))) ∧ (((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3))) = ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3)))))))
  (h2 : Tendsto (fun x : ℝ => ((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))))))
  (h3 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))) (𝓝[≠] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))) (𝓝[≠] 1) (𝓝 (3 /. 6)) := by
  sorry

theorem proof_gap_exercise_419_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3)) = ((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3)))) ∧ (((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3))) = ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3)))))))
  (h2 : Tendsto (fun x : ℝ => ((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))))))
  (h3 : Tendsto (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))) (𝓝[≠] 1) (𝓝 (3 /. 6)))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))) (𝓝[≠] 1) (𝓝 L))
  : (3 /. 6) = (1 /. 2) := by
  sorry

theorem proof_gap_exercise_419_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 1)) → ((((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3)) = ((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3)))) ∧ (((((x - 1) ^ (2 : ℕ)) * (x + 2)) /. (((x - 1) ^ (2 : ℕ)) * (((x ^ (2 : ℕ)) + (2 * x)) + 3))) = ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3)))))))
  (h2 : Tendsto (fun x : ℝ => ((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3))) (𝓝[≠] 1) (𝓝 ((𝓝[≠] 1).limUnder (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))))))
  (h3 : Tendsto (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))) (𝓝[≠] 1) (𝓝 (3 /. 6)))
  (h4 : (3 /. 6) = (1 /. 2))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => ((x + 2) /. (((x ^ (2 : ℕ)) + (2 * x)) + 3))) (𝓝[≠] 1) (𝓝 L))
  : Tendsto (fun x : ℝ => ((((x ^ (3 : ℕ)) - (3 * x)) + 2) /. (((x ^ (4 : ℕ)) - (4 * x)) + 3))) (𝓝[≠] 1) (𝓝 (1 /. 2)) := by
  sorry
