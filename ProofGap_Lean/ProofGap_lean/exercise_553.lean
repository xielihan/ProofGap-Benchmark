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

-- exercise: exercise_553

theorem proof_gap_exercise_553_1
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → (((n ^ (2 : ℕ)) * ((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1))))) = (((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_553_2
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → (((n ^ (2 : ℕ)) * ((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1))))) = (((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = (((Real.rpow x (1 /. (n + 1))) * ((Real.rpow x (1 /. (n * (n + 1)))) - 1)) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n))))))) := by
  sorry

theorem proof_gap_exercise_553_3
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → (((n ^ (2 : ℕ)) * ((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1))))) = (((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = (((Real.rpow x (1 /. (n + 1))) * ((Real.rpow x (1 /. (n * (n + 1)))) - 1)) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n))))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = ((((Real.rpow x (1 /. (n * (n + 1)))) - 1) /. (1 /. (n * (n + 1)))) * (((Real.rpow x (1 /. (n + 1))) * (1 /. (n * (n + 1)))) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n)))))))) := by
  sorry

theorem proof_gap_exercise_553_4
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → (((n ^ (2 : ℕ)) * ((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1))))) = (((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = (((Real.rpow x (1 /. (n + 1))) * ((Real.rpow x (1 /. (n * (n + 1)))) - 1)) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = ((((Real.rpow x (1 /. (n * (n + 1)))) - 1) /. (1 /. (n * (n + 1)))) * (((Real.rpow x (1 /. (n + 1))) * (1 /. (n * (n + 1)))) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n)))))))))
  : Tendsto (fun n : ℕ => (((Real.rpow x (1 /. (n * (n + 1)))) - 1) /. (1 /. (n * (n + 1))))) atTop (𝓝 (Real.log x)) := by
  sorry

theorem proof_gap_exercise_553_5
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → (((n ^ (2 : ℕ)) * ((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1))))) = (((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = (((Real.rpow x (1 /. (n + 1))) * ((Real.rpow x (1 /. (n * (n + 1)))) - 1)) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = ((((Real.rpow x (1 /. (n * (n + 1)))) - 1) /. (1 /. (n * (n + 1)))) * (((Real.rpow x (1 /. (n + 1))) * (1 /. (n * (n + 1)))) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n)))))))))
  (h5 : Tendsto (fun n : ℕ => (((Real.rpow x (1 /. (n * (n + 1)))) - 1) /. (1 /. (n * (n + 1))))) atTop (𝓝 (Real.log x)))
  : Tendsto (fun n : ℕ => (((Real.rpow x (1 /. (n + 1))) * (1 /. (n * (n + 1)))) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n))))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_553_6
  (x : ℝ)
  (h1 : (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → (((n ^ (2 : ℕ)) * ((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1))))) = (((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = (((Real.rpow x (1 /. (n + 1))) * ((Real.rpow x (1 /. (n * (n + 1)))) - 1)) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n))))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0)) → ((((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))) /. (1 /. (n ^ (2 : ℕ)))) = ((((Real.rpow x (1 /. (n * (n + 1)))) - 1) /. (1 /. (n * (n + 1)))) * (((Real.rpow x (1 /. (n + 1))) * (1 /. (n * (n + 1)))) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n)))))))))
  (h5 : Tendsto (fun n : ℕ => (((Real.rpow x (1 /. (n * (n + 1)))) - 1) /. (1 /. (n * (n + 1))))) atTop (𝓝 (Real.log x)))
  (h6 : Tendsto (fun n : ℕ => (((Real.rpow x (1 /. (n + 1))) * (1 /. (n * (n + 1)))) /. (((1 /. (n * (n + 1))) + (1 /. (n ^ (2 : ℕ)))) - (1 /. ((n ^ (2 : ℕ)) + n))))) atTop (𝓝 1))
  : Tendsto (fun n : ℕ => ((n ^ (2 : ℕ)) * ((Real.rpow x (1 /. n)) - (Real.rpow x (1 /. (n + 1)))))) atTop (𝓝 (Real.log x)) := by
  sorry
