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

-- exercise: exercise_543

theorem proof_gap_exercise_543_1
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((Real.rpow x x) - (Real.rpow a a)) /. (x - a)) = (((Real.rpow a a) * (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) * (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)))))) := by
  sorry

theorem proof_gap_exercise_543_2
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((Real.rpow x x) - (Real.rpow a a)) /. (x - a)) = (((Real.rpow a a) * (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) * (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)) = ((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a))))) := by
  sorry

theorem proof_gap_exercise_543_3
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((Real.rpow x x) - (Real.rpow a a)) /. (x - a)) = (((Real.rpow a a) * (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) * (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)) = ((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → (((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a)) = (((x /. a) * ((Real.log (1 + ((x - a) /. a))) /. ((x - a) /. a))) + (Real.log a))))) := by
  sorry

theorem proof_gap_exercise_543_4
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) ∧ ((x * (Real.log x)) ≠ (a * (Real.log a)))) → ((((Real.rpow x x) - (Real.rpow a a)) /. (x - a)) = (((Real.rpow a a) * (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) * (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)) = ((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → (((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a)) = (((x /. a) * ((Real.log (1 + ((x - a) /. a))) /. ((x - a) /. a))) + (Real.log a))))))
  : Tendsto (fun x : ℝ => (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a))) (𝓝[≠] a) (𝓝 (1 + (Real.log a))) := by
  sorry

theorem proof_gap_exercise_543_5
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((Real.rpow x x) - (Real.rpow a a)) /. (x - a)) = (((Real.rpow a a) * (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) * (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)) = ((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → (((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a)) = (((x /. a) * ((Real.log (1 + ((x - a) /. a))) /. ((x - a) /. a))) + (Real.log a))))))
  (h5 : Tendsto (fun x : ℝ => (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a))) (𝓝[≠] a) (𝓝 (1 + (Real.log a))))
  : (1 + (Real.log a)) = (Real.log ((Real.exp 1) * a)) := by
  sorry

theorem proof_gap_exercise_543_6
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) ∧ ((x * (Real.log x)) ≠ (a * (Real.log a)))) → ((((Real.rpow x x) - (Real.rpow a a)) /. (x - a)) = (((Real.rpow a a) * (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) * (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)) = ((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → (((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a)) = (((x /. a) * ((Real.log (1 + ((x - a) /. a))) /. ((x - a) /. a))) + (Real.log a))))))
  (h5 : Tendsto (fun x : ℝ => (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a))) (𝓝[≠] a) (𝓝 (1 + (Real.log a))))
  (h6 : (1 + (Real.log a)) = (Real.log ((Real.exp 1) * a)))
  : Tendsto (fun x : ℝ => (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) (𝓝[≠] a) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_543_7
  (a : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (forall (x : ℝ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) ∧ ((x * (Real.log x)) ≠ (a * (Real.log a)))) → ((((Real.rpow x x) - (Real.rpow a a)) /. (x - a)) = (((Real.rpow a a) * (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) * (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → ((((x * (Real.log x)) - (a * (Real.log a))) /. (x - a)) = ((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) ∧ (x ≠ a)) → (((((x * (Real.log x)) - (x * (Real.log a))) /. (x - a)) + (Real.log a)) = (((x /. a) * ((Real.log (1 + ((x - a) /. a))) /. ((x - a) /. a))) + (Real.log a))))))
  (h5 : Tendsto (fun x : ℝ => (((x * (Real.log x)) - (a * (Real.log a))) /. (x - a))) (𝓝[≠] a) (𝓝 (1 + (Real.log a))))
  (h6 : (1 + (Real.log a)) = (Real.log ((Real.exp 1) * a)))
  (h7 : Tendsto (fun x : ℝ => (((Real.exp ((x * (Real.log x)) - (a * (Real.log a)))) - 1) /. ((x * (Real.log x)) - (a * (Real.log a))))) (𝓝[≠] a) (𝓝 1))
  : Tendsto (fun x : ℝ => (((Real.rpow x x) - (Real.rpow a a)) /. (x - a))) (𝓝[≠] a) (𝓝 ((Real.rpow a a) * (Real.log ((Real.exp 1) * a)))) := by
  sorry
