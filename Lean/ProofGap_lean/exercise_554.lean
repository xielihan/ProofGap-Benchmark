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

-- exercise: exercise_554

theorem proof_gap_exercise_554_1
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  : (forall (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((Real.rpow b (1 /. n)) - 1) ≠ 0)) → (((((a - 1) + (Real.rpow b (1 /. n))) /. a) ^ n) = (Real.rpow (1 + (1 /. (a /. ((Real.rpow b (1 /. n)) - 1)))) (((a /. ((Real.rpow b (1 /. n)) - 1)) * (((Real.rpow b (1 /. n)) - 1) /. (1 /. n))) * (1 /. a)))))) := by
  sorry

theorem proof_gap_exercise_554_2
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((Real.rpow b (1 /. n)) - 1) ≠ 0)) → (((((a - 1) + (Real.rpow b (1 /. n))) /. a) ^ n) = (Real.rpow (1 + (1 /. (a /. ((Real.rpow b (1 /. n)) - 1)))) (((a /. ((Real.rpow b (1 /. n)) - 1)) * (((Real.rpow b (1 /. n)) - 1) /. (1 /. n))) * (1 /. a)))))))
  : Tendsto (fun n : ℕ => (((Real.rpow b (1 /. n)) - 1) /. (1 /. n))) atTop (𝓝 (Real.log b)) := by
  sorry

theorem proof_gap_exercise_554_3
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((Real.rpow b (1 /. n)) - 1) ≠ 0)) → (((((a - 1) + (Real.rpow b (1 /. n))) /. a) ^ n) = (Real.rpow (1 + (1 /. (a /. ((Real.rpow b (1 /. n)) - 1)))) (((a /. ((Real.rpow b (1 /. n)) - 1)) * (((Real.rpow b (1 /. n)) - 1) /. (1 /. n))) * (1 /. a)))))))
  (h4 : Tendsto (fun n : ℕ => (((Real.rpow b (1 /. n)) - 1) /. (1 /. n))) atTop (𝓝 (Real.log b)))
  : Tendsto (fun n : ℕ => (Real.rpow (((a - 1) + (Real.rpow b (1 /. n))) /. a) n)) atTop (𝓝 (Real.exp ((1 /. a) * (Real.log b)))) := by
  sorry

theorem proof_gap_exercise_554_4
  (a : ℝ)
  (b : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (b ∈ (Set.univ : Set ℝ)) ∧ (b > 0))
  (h3 : (forall (n : ℕ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (((Real.rpow b (1 /. n)) - 1) ≠ 0)) → (((((a - 1) + (Real.rpow b (1 /. n))) /. a) ^ n) = (Real.rpow (1 + (1 /. (a /. ((Real.rpow b (1 /. n)) - 1)))) (((a /. ((Real.rpow b (1 /. n)) - 1)) * (((Real.rpow b (1 /. n)) - 1) /. (1 /. n))) * (1 /. a)))))))
  (h4 : Tendsto (fun n : ℕ => (((Real.rpow b (1 /. n)) - 1) /. (1 /. n))) atTop (𝓝 (Real.log b)))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (((a - 1) + (Real.rpow b (1 /. n))) /. a) n)) atTop (𝓝 (Real.exp ((1 /. a) * (Real.log b)))))
  : (Real.exp ((1 /. a) * (Real.log b))) = (Real.rpow b (1 /. a)) := by
  sorry
