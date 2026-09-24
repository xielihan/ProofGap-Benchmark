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

-- exercise: exercise_521

theorem proof_gap_exercise_521_1
  : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((Real.cos (2 * x)) ≠ 0)) ∧ (((Real.cos x) - (Real.cos (2 * x))) ≠ 0)) → ((Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ)))) = (Real.rpow (1 + (1 /. ((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))))) (((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))) * (((Real.cos x) - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (Real.cos (2 * x))))))))) := by
  sorry

theorem proof_gap_exercise_521_2
  (h1 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((Real.cos (2 * x)) ≠ 0)) ∧ (((Real.cos x) - (Real.cos (2 * x))) ≠ 0)) → ((Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ)))) = (Real.rpow (1 + (1 /. ((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))))) (((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))) * (((Real.cos x) - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (Real.cos (2 * x))))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = ((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_521_3
  (h1 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((Real.cos (2 * x)) ≠ 0)) ∧ (((Real.cos x) - (Real.cos (2 * x))) ≠ 0)) → ((Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ)))) = (Real.rpow (1 + (1 /. ((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))))) (((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))) * (((Real.cos x) - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (Real.cos (2 * x))))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = ((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))) := by
  sorry

theorem proof_gap_exercise_521_4
  (h1 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((Real.cos (2 * x)) ≠ 0)) ∧ (((Real.cos x) - (Real.cos (2 * x))) ≠ 0)) → ((Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ)))) = (Real.rpow (1 + (1 /. ((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))))) (((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))) * (((Real.cos x) - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (Real.cos (2 * x))))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = ((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))) := by
  sorry

theorem proof_gap_exercise_521_5
  (h1 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((Real.cos (2 * x)) ≠ 0)) ∧ (((Real.cos x) - (Real.cos (2 * x))) ≠ 0)) → ((Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ)))) = (Real.rpow (1 + (1 /. ((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))))) (((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))) * (((Real.cos x) - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (Real.cos (2 * x))))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = ((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x)))) = (((1 + (2 * (Real.cos x))) /. 2) * (((Real.sin (x /. 2)) /. (x /. 2)) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_521_6
  (h1 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((Real.cos (2 * x)) ≠ 0)) ∧ (((Real.cos x) - (Real.cos (2 * x))) ≠ 0)) → ((Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ)))) = (Real.rpow (1 + (1 /. ((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))))) (((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))) * (((Real.cos x) - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (Real.cos (2 * x))))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = ((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x)))) = (((1 + (2 * (Real.cos x))) /. 2) * (((Real.sin (x /. 2)) /. (x /. 2)) ^ (2 : ℕ)))))))
  : Tendsto (fun x : ℝ => (((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (3 /. 2)) := by
  sorry

theorem proof_gap_exercise_521_7
  (h1 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((Real.cos (2 * x)) ≠ 0)) ∧ (((Real.cos x) - (Real.cos (2 * x))) ≠ 0)) → ((Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ)))) = (Real.rpow (1 + (1 /. ((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))))) (((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))) * (((Real.cos x) - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (Real.cos (2 * x))))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = ((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x)))) = (((1 + (2 * (Real.cos x))) /. 2) * (((Real.sin (x /. 2)) /. (x /. 2)) ^ (2 : ℕ)))))))
  (h6 : Tendsto (fun x : ℝ => (((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (3 /. 2)))
  : Tendsto (fun x : ℝ => (Real.cos (2 * x))) (𝓝[≠] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_521_8
  (h1 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ ((Real.cos (2 * x)) ≠ 0)) ∧ (((Real.cos x) - (Real.cos (2 * x))) ≠ 0)) → ((Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ)))) = (Real.rpow (1 + (1 /. ((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))))) (((Real.cos (2 * x)) /. ((Real.cos x) - (Real.cos (2 * x)))) * (((Real.cos x) - (Real.cos (2 * x))) /. ((x ^ (2 : ℕ)) * (Real.cos (2 * x))))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = ((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → (((((Real.cos x) + 1) - (2 * ((Real.cos x) ^ (2 : ℕ)))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ))) = (((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x))))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((((1 - (Real.cos x)) /. (x ^ (2 : ℕ))) * (1 + (2 * (Real.cos x)))) = (((1 + (2 * (Real.cos x))) /. 2) * (((Real.sin (x /. 2)) /. (x /. 2)) ^ (2 : ℕ)))))))
  (h6 : Tendsto (fun x : ℝ => (((Real.cos x) - (Real.cos (2 * x))) /. (x ^ (2 : ℕ)))) (𝓝[≠] 0) (𝓝 (3 /. 2)))
  (h7 : Tendsto (fun x : ℝ => (Real.cos (2 * x))) (𝓝[≠] 0) (𝓝 1))
  : Tendsto (fun x : ℝ => (Real.rpow ((Real.cos x) /. (Real.cos (2 * x))) (1 /. (x ^ (2 : ℕ))))) (𝓝[≠] 0) (𝓝 (Real.exp (3 /. 2))) := by
  sorry
