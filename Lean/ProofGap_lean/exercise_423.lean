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

-- exercise: exercise_423

theorem proof_gap_exercise_423_1
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → (((((x ^ (2 : ℕ)) - x) - 2) = ((x - 2) * (x + 1))) ∧ ((((x ^ (3 : ℕ)) - (12 * x)) + 16) = (((x - 2) ^ (2 : ℕ)) * (x + 4)))))) := by
  sorry

theorem proof_gap_exercise_423_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → (((((x ^ (2 : ℕ)) - x) - 2) = ((x - 2) * (x + 1))) ∧ ((((x ^ (3 : ℕ)) - (12 * x)) + 16) = (((x - 2) ^ (2 : ℕ)) * (x + 4)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → ((((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ))) = ((((x - 2) ^ (20 : ℕ)) * ((x + 1) ^ (20 : ℕ))) /. (((x - 2) ^ (20 : ℕ)) * ((x + 4) ^ (10 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_423_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → (((((x ^ (2 : ℕ)) - x) - 2) = ((x - 2) * (x + 1))) ∧ ((((x ^ (3 : ℕ)) - (12 * x)) + 16) = (((x - 2) ^ (2 : ℕ)) * (x + 4)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → ((((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ))) = ((((x - 2) ^ (20 : ℕ)) * ((x + 1) ^ (20 : ℕ))) /. (((x - 2) ^ (20 : ℕ)) * ((x + 4) ^ (10 : ℕ))))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 ((𝓝[≠] 2).limUnder (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_423_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → (((((x ^ (2 : ℕ)) - x) - 2) = ((x - 2) * (x + 1))) ∧ ((((x ^ (3 : ℕ)) - (12 * x)) + 16) = (((x - 2) ^ (2 : ℕ)) * (x + 4)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → ((((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ))) = ((((x - 2) ^ (20 : ℕ)) * ((x + 1) ^ (20 : ℕ))) /. (((x - 2) ^ (20 : ℕ)) * ((x + 4) ^ (10 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => (((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 ((𝓝[≠] 2).limUnder (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))))))
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 L))
  : Tendsto (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 (((3 : ℕ) ^ (20 : ℕ)) /. ((6 : ℕ) ^ (10 : ℕ)))) := by
  sorry

theorem proof_gap_exercise_423_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → (((((x ^ (2 : ℕ)) - x) - 2) = ((x - 2) * (x + 1))) ∧ ((((x ^ (3 : ℕ)) - (12 * x)) + 16) = (((x - 2) ^ (2 : ℕ)) * (x + 4)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → ((((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ))) = ((((x - 2) ^ (20 : ℕ)) * ((x + 1) ^ (20 : ℕ))) /. (((x - 2) ^ (20 : ℕ)) * ((x + 4) ^ (10 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => (((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 ((𝓝[≠] 2).limUnder (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))))))
  (h4 : Tendsto (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 (((3 : ℕ) ^ (20 : ℕ)) /. ((6 : ℕ) ^ (10 : ℕ)))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 L))
  : (((3 : ℕ) ^ (20 : ℕ)) /. ((6 : ℕ) ^ (10 : ℕ))) = ((3 /. 2) ^ (10 : ℕ)) := by
  sorry

theorem proof_gap_exercise_423_6
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → (((((x ^ (2 : ℕ)) - x) - 2) = ((x - 2) * (x + 1))) ∧ ((((x ^ (3 : ℕ)) - (12 * x)) + 16) = (((x - 2) ^ (2 : ℕ)) * (x + 4)))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 2)) → ((((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ))) = ((((x - 2) ^ (20 : ℕ)) * ((x + 1) ^ (20 : ℕ))) /. (((x - 2) ^ (20 : ℕ)) * ((x + 4) ^ (10 : ℕ))))))))
  (h3 : Tendsto (fun x : ℝ => (((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 ((𝓝[≠] 2).limUnder (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))))))
  (h4 : Tendsto (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 (((3 : ℕ) ^ (20 : ℕ)) /. ((6 : ℕ) ^ (10 : ℕ)))))
  (h5 : (((3 : ℕ) ^ (20 : ℕ)) /. ((6 : ℕ) ^ (10 : ℕ))) = ((3 /. 2) ^ (10 : ℕ)))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((x + 1) ^ (20 : ℕ)) /. ((x + 4) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 L))
  : Tendsto (fun x : ℝ => (((((x ^ (2 : ℕ)) - x) - 2) ^ (20 : ℕ)) /. ((((x ^ (3 : ℕ)) - (12 * x)) + 16) ^ (10 : ℕ)))) (𝓝[≠] 2) (𝓝 ((3 /. 2) ^ (10 : ℕ))) := by
  sorry
