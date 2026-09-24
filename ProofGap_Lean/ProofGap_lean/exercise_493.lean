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

-- exercise: exercise_493

theorem proof_gap_exercise_493_1
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) + 1))))) := by
  sorry

theorem proof_gap_exercise_493_2
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) + 1))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) - 1))))) := by
  sorry

theorem proof_gap_exercise_493_3
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) + 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) - 1))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((2 * (Real.sin x)) - 1) ≠ 0)) ∧ (((Real.sin x) - 1) ≠ 0)) → (((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) /. (((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1)) = (((Real.sin x) + 1) /. ((Real.sin x) - 1))))) := by
  sorry

theorem proof_gap_exercise_493_4
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) + 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) - 1))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((2 * (Real.sin x)) - 1) ≠ 0)) ∧ (((Real.sin x) - 1) ≠ 0)) → (((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) /. (((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1)) = (((Real.sin x) + 1) /. ((Real.sin x) - 1))))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.sin x) + 1) /. ((Real.sin x) - 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 L) ∧ (Tendsto (fun x : ℝ => ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) /. (((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 ((𝓝[≠] (Real.pi /. 6)).limUnder (fun x : ℝ => (((Real.sin x) + 1) /. ((Real.sin x) - 1))))))) := by
  sorry

theorem proof_gap_exercise_493_5
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) + 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) - 1))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((2 * (Real.sin x)) - 1) ≠ 0)) ∧ (((Real.sin x) - 1) ≠ 0)) → (((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) /. (((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1)) = (((Real.sin x) + 1) /. ((Real.sin x) - 1))))))
  (h4 : Tendsto (fun x : ℝ => ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) /. (((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 ((𝓝[≠] (Real.pi /. 6)).limUnder (fun x : ℝ => (((Real.sin x) + 1) /. ((Real.sin x) - 1))))))
  (h5 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.sin x) + 1) /. ((Real.sin x) - 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 L))
  : Tendsto (fun x : ℝ => (((Real.sin x) + 1) /. ((Real.sin x) - 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 (-(3 : ℝ))) := by
  sorry

theorem proof_gap_exercise_493_6
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) + 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1) = (((2 * (Real.sin x)) - 1) * ((Real.sin x) - 1))))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (((2 * (Real.sin x)) - 1) ≠ 0)) ∧ (((Real.sin x) - 1) ≠ 0)) → (((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) /. (((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1)) = (((Real.sin x) + 1) /. ((Real.sin x) - 1))))))
  (h4 : Tendsto (fun x : ℝ => ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) /. (((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 ((𝓝[≠] (Real.pi /. 6)).limUnder (fun x : ℝ => (((Real.sin x) + 1) /. ((Real.sin x) - 1))))))
  (h5 : Tendsto (fun x : ℝ => (((Real.sin x) + 1) /. ((Real.sin x) - 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 (-(3 : ℝ))))
  (h6 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.sin x) + 1) /. ((Real.sin x) - 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 L))
  : Tendsto (fun x : ℝ => ((((2 * ((Real.sin x) ^ (2 : ℕ))) + (Real.sin x)) - 1) /. (((2 * ((Real.sin x) ^ (2 : ℕ))) - (3 * (Real.sin x))) + 1))) (𝓝[≠] (Real.pi /. 6)) (𝓝 (-(3 : ℝ))) := by
  sorry
